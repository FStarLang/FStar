open Prims
let (fetch_eq_side :
  unit ->
    ((FStar_Reflection_Types.term * FStar_Reflection_Types.term), unit)
      FStar_Tactics_Effect.tac_repr)
  =
  fun uu___ ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Range.mk_range "FStar.Tactics.PatternMatching.fst"
         (Prims.of_int (63)) (Prims.of_int (10)) (Prims.of_int (63))
         (Prims.of_int (21)))
      (FStar_Range.mk_range "FStar.Tactics.PatternMatching.fst"
         (Prims.of_int (64)) (Prims.of_int (2)) (Prims.of_int (88))
         (Prims.of_int (39))) (Obj.magic (FStar_Tactics_Derived.cur_goal ()))
      (fun uu___1 ->
         (fun g ->
            Obj.magic
              (FStar_Tactics_Effect.tac_bind
                 (FStar_Range.mk_range "FStar.Tactics.PatternMatching.fst"
                    (Prims.of_int (64)) (Prims.of_int (8))
                    (Prims.of_int (64)) (Prims.of_int (17)))
                 (FStar_Range.mk_range "FStar.Tactics.PatternMatching.fst"
                    (Prims.of_int (64)) (Prims.of_int (2))
                    (Prims.of_int (88)) (Prims.of_int (39)))
                 (Obj.magic (FStar_Tactics_Builtins.inspect g))
                 (fun uu___1 ->
                    (fun uu___1 ->
                       match uu___1 with
                       | FStar_Reflection_Data.Tv_App (squash, (g1, uu___2))
                           ->
                           Obj.magic
                             (Obj.repr
                                (FStar_Tactics_Effect.tac_bind
                                   (FStar_Range.mk_range
                                      "FStar.Tactics.PatternMatching.fst"
                                      (Prims.of_int (66)) (Prims.of_int (11))
                                      (Prims.of_int (66)) (Prims.of_int (25)))
                                   (FStar_Range.mk_range
                                      "FStar.Tactics.PatternMatching.fst"
                                      (Prims.of_int (66)) (Prims.of_int (4))
                                      (Prims.of_int (87)) (Prims.of_int (51)))
                                   (Obj.magic
                                      (FStar_Tactics_Builtins.inspect squash))
                                   (fun uu___3 ->
                                      (fun uu___3 ->
                                         match uu___3 with
                                         | FStar_Reflection_Data.Tv_UInst
                                             (squash1, uu___4) ->
                                             Obj.magic
                                               (Obj.repr
                                                  (if
                                                     (FStar_Reflection_Derived.fv_to_string
                                                        squash1)
                                                       =
                                                       (FStar_Reflection_Derived.flatten_name
                                                          FStar_Reflection_Const.squash_qn)
                                                   then
                                                     Obj.repr
                                                       (FStar_Tactics_Effect.tac_bind
                                                          (FStar_Range.mk_range
                                                             "FStar.Tactics.PatternMatching.fst"
                                                             (Prims.of_int (70))
                                                             (Prims.of_int (16))
                                                             (Prims.of_int (70))
                                                             (Prims.of_int (25)))
                                                          (FStar_Range.mk_range
                                                             "FStar.Tactics.PatternMatching.fst"
                                                             (Prims.of_int (70))
                                                             (Prims.of_int (9))
                                                             (Prims.of_int (85))
                                                             (Prims.of_int (48)))
                                                          (Obj.magic
                                                             (FStar_Tactics_Builtins.inspect
                                                                g1))
                                                          (fun uu___5 ->
                                                             (fun uu___5 ->
                                                                match uu___5
                                                                with
                                                                | FStar_Reflection_Data.Tv_App
                                                                    (eq_type_x,
                                                                    (y,
                                                                    uu___6))
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (72))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (72))
                                                                    (Prims.of_int (36)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (72))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (84))
                                                                    (Prims.of_int (39)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Builtins.inspect
                                                                    eq_type_x))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    uu___7 ->
                                                                    match uu___7
                                                                    with
                                                                    | 
                                                                    FStar_Reflection_Data.Tv_App
                                                                    (eq_type,
                                                                    (x,
                                                                    uu___8))
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (74))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (74))
                                                                    (Prims.of_int (37)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (74))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (83))
                                                                    (Prims.of_int (42)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Builtins.inspect
                                                                    eq_type))
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun
                                                                    uu___9 ->
                                                                    match uu___9
                                                                    with
                                                                    | 
                                                                    FStar_Reflection_Data.Tv_App
                                                                    (eq,
                                                                    (typ,
                                                                    uu___10))
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (76))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (76))
                                                                    (Prims.of_int (35)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (76))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (82))
                                                                    (Prims.of_int (55)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Builtins.inspect
                                                                    eq))
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    match uu___11
                                                                    with
                                                                    | 
                                                                    FStar_Reflection_Data.Tv_UInst
                                                                    (eq1,
                                                                    uu___12)
                                                                    ->
                                                                    if
                                                                    (FStar_Reflection_Derived.fv_to_string
                                                                    eq1) =
                                                                    (FStar_Reflection_Derived.flatten_name
                                                                    FStar_Reflection_Const.eq2_qn)
                                                                    then
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___13
                                                                    -> (x, y))
                                                                    else
                                                                    FStar_Tactics_Derived.fail
                                                                    "not an equality"
                                                                    | 
                                                                    FStar_Reflection_Data.Tv_FVar
                                                                    eq1 ->
                                                                    if
                                                                    (FStar_Reflection_Derived.fv_to_string
                                                                    eq1) =
                                                                    (FStar_Reflection_Derived.flatten_name
                                                                    FStar_Reflection_Const.eq2_qn)
                                                                    then
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___12
                                                                    -> (x, y))
                                                                    else
                                                                    FStar_Tactics_Derived.fail
                                                                    "not an equality"
                                                                    | 
                                                                    uu___12
                                                                    ->
                                                                    FStar_Tactics_Derived.fail
                                                                    "not an app2 of fvar: ")))
                                                                    | 
                                                                    uu___10
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Derived.fail
                                                                    "not an app3")))
                                                                    uu___9)))
                                                                    | 
                                                                    uu___8 ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Derived.fail
                                                                    "not an app2")))
                                                                    uu___7)))
                                                                | uu___6 ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Derived.fail
                                                                    "not an app under squash")))
                                                               uu___5))
                                                   else
                                                     Obj.repr
                                                       (FStar_Tactics_Derived.fail
                                                          "not a squash")))
                                         | FStar_Reflection_Data.Tv_FVar
                                             squash1 ->
                                             Obj.magic
                                               (Obj.repr
                                                  (if
                                                     (FStar_Reflection_Derived.fv_to_string
                                                        squash1)
                                                       =
                                                       (FStar_Reflection_Derived.flatten_name
                                                          FStar_Reflection_Const.squash_qn)
                                                   then
                                                     Obj.repr
                                                       (FStar_Tactics_Effect.tac_bind
                                                          (FStar_Range.mk_range
                                                             "FStar.Tactics.PatternMatching.fst"
                                                             (Prims.of_int (70))
                                                             (Prims.of_int (16))
                                                             (Prims.of_int (70))
                                                             (Prims.of_int (25)))
                                                          (FStar_Range.mk_range
                                                             "FStar.Tactics.PatternMatching.fst"
                                                             (Prims.of_int (70))
                                                             (Prims.of_int (9))
                                                             (Prims.of_int (85))
                                                             (Prims.of_int (48)))
                                                          (Obj.magic
                                                             (FStar_Tactics_Builtins.inspect
                                                                g1))
                                                          (fun uu___4 ->
                                                             (fun uu___4 ->
                                                                match uu___4
                                                                with
                                                                | FStar_Reflection_Data.Tv_App
                                                                    (eq_type_x,
                                                                    (y,
                                                                    uu___5))
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (72))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (72))
                                                                    (Prims.of_int (36)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (72))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (84))
                                                                    (Prims.of_int (39)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Builtins.inspect
                                                                    eq_type_x))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    uu___6 ->
                                                                    match uu___6
                                                                    with
                                                                    | 
                                                                    FStar_Reflection_Data.Tv_App
                                                                    (eq_type,
                                                                    (x,
                                                                    uu___7))
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (74))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (74))
                                                                    (Prims.of_int (37)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (74))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (83))
                                                                    (Prims.of_int (42)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Builtins.inspect
                                                                    eq_type))
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun
                                                                    uu___8 ->
                                                                    match uu___8
                                                                    with
                                                                    | 
                                                                    FStar_Reflection_Data.Tv_App
                                                                    (eq,
                                                                    (typ,
                                                                    uu___9))
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (76))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (76))
                                                                    (Prims.of_int (35)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (76))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (82))
                                                                    (Prims.of_int (55)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Builtins.inspect
                                                                    eq))
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    match uu___10
                                                                    with
                                                                    | 
                                                                    FStar_Reflection_Data.Tv_UInst
                                                                    (eq1,
                                                                    uu___11)
                                                                    ->
                                                                    if
                                                                    (FStar_Reflection_Derived.fv_to_string
                                                                    eq1) =
                                                                    (FStar_Reflection_Derived.flatten_name
                                                                    FStar_Reflection_Const.eq2_qn)
                                                                    then
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___12
                                                                    -> (x, y))
                                                                    else
                                                                    FStar_Tactics_Derived.fail
                                                                    "not an equality"
                                                                    | 
                                                                    FStar_Reflection_Data.Tv_FVar
                                                                    eq1 ->
                                                                    if
                                                                    (FStar_Reflection_Derived.fv_to_string
                                                                    eq1) =
                                                                    (FStar_Reflection_Derived.flatten_name
                                                                    FStar_Reflection_Const.eq2_qn)
                                                                    then
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___11
                                                                    -> (x, y))
                                                                    else
                                                                    FStar_Tactics_Derived.fail
                                                                    "not an equality"
                                                                    | 
                                                                    uu___11
                                                                    ->
                                                                    FStar_Tactics_Derived.fail
                                                                    "not an app2 of fvar: ")))
                                                                    | 
                                                                    uu___9 ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Derived.fail
                                                                    "not an app3")))
                                                                    uu___8)))
                                                                    | 
                                                                    uu___7 ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Derived.fail
                                                                    "not an app2")))
                                                                    uu___6)))
                                                                | uu___5 ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Derived.fail
                                                                    "not an app under squash")))
                                                               uu___4))
                                                   else
                                                     Obj.repr
                                                       (FStar_Tactics_Derived.fail
                                                          "not a squash")))
                                         | uu___4 ->
                                             Obj.magic
                                               (Obj.repr
                                                  (FStar_Tactics_Derived.fail
                                                     "not an app of fvar at top level")))
                                        uu___3)))
                       | uu___2 ->
                           Obj.magic
                             (Obj.repr
                                (FStar_Tactics_Derived.fail
                                   "not an app at top level"))) uu___1)))
           uu___1)
let mustfail :
  'a .
    (unit -> ('a, unit) FStar_Tactics_Effect.tac_repr) ->
      Prims.string -> (unit, unit) FStar_Tactics_Effect.tac_repr
  =
  fun t ->
    fun message ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Range.mk_range "FStar.Tactics.PatternMatching.fst"
           (Prims.of_int (130)) (Prims.of_int (10)) (Prims.of_int (130))
           (Prims.of_int (18)))
        (FStar_Range.mk_range "FStar.Tactics.PatternMatching.fst"
           (Prims.of_int (130)) (Prims.of_int (4)) (Prims.of_int (132))
           (Prims.of_int (16))) (Obj.magic (FStar_Tactics_Derived.trytac t))
        (fun uu___ ->
           match uu___ with
           | FStar_Pervasives_Native.Some uu___1 ->
               FStar_Tactics_Derived.fail message
           | FStar_Pervasives_Native.None ->
               FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> ()))
let (implies_intro' : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Range.mk_range "FStar.Tactics.PatternMatching.fst"
         (Prims.of_int (138)) (Prims.of_int (10)) (Prims.of_int (138))
         (Prims.of_int (26)))
      (FStar_Range.mk_range "FStar.Tactics.PatternMatching.fst"
         (Prims.of_int (138)) (Prims.of_int (30)) (Prims.of_int (138))
         (Prims.of_int (32)))
      (Obj.magic (FStar_Tactics_Logic.implies_intro ()))
      (fun uu___1 -> FStar_Tactics_Effect.lift_div_tac (fun uu___2 -> ()))
let repeat' :
  'a .
    (unit -> ('a, unit) FStar_Tactics_Effect.tac_repr) ->
      (unit, unit) FStar_Tactics_Effect.tac_repr
  =
  fun f ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Range.mk_range "FStar.Tactics.PatternMatching.fst"
         (Prims.of_int (141)) (Prims.of_int (10)) (Prims.of_int (141))
         (Prims.of_int (18)))
      (FStar_Range.mk_range "FStar.Tactics.PatternMatching.fst"
         (Prims.of_int (141)) (Prims.of_int (22)) (Prims.of_int (141))
         (Prims.of_int (24))) (Obj.magic (FStar_Tactics_Derived.repeat f))
      (fun uu___ -> FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> ()))
let (and_elim' :
  FStar_Reflection_Types.binder -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun h ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Range.mk_range "FStar.Tactics.PatternMatching.fst"
         (Prims.of_int (144)) (Prims.of_int (2)) (Prims.of_int (144))
         (Prims.of_int (43)))
      (FStar_Range.mk_range "FStar.Tactics.PatternMatching.fst"
         (Prims.of_int (145)) (Prims.of_int (2)) (Prims.of_int (145))
         (Prims.of_int (9)))
      (Obj.magic
         (FStar_Tactics_Effect.tac_bind
            (FStar_Range.mk_range "FStar.Tactics.PatternMatching.fst"
               (Prims.of_int (144)) (Prims.of_int (11)) (Prims.of_int (144))
               (Prims.of_int (43)))
            (FStar_Range.mk_range "FStar.Tactics.PatternMatching.fst"
               (Prims.of_int (144)) (Prims.of_int (2)) (Prims.of_int (144))
               (Prims.of_int (43)))
            (Obj.magic
               (FStar_Tactics_Builtins.pack
                  (FStar_Reflection_Data.Tv_Var
                     (FStar_Reflection_Derived.bv_of_binder h))))
            (fun uu___ ->
               (fun uu___ -> Obj.magic (FStar_Tactics_Logic.and_elim uu___))
                 uu___)))
      (fun uu___ ->
         (fun uu___ -> Obj.magic (FStar_Tactics_Builtins.clear h)) uu___)
let exact_hyp :
  'a .
    FStar_Reflection_Types.binder ->
      (unit, unit) FStar_Tactics_Effect.tac_repr
  =
  fun h ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Range.mk_range "FStar.Tactics.PatternMatching.fst"
         (Prims.of_int (149)) (Prims.of_int (11)) (Prims.of_int (149))
         (Prims.of_int (48)))
      (FStar_Range.mk_range "FStar.Tactics.PatternMatching.fst"
         (Prims.of_int (150)) (Prims.of_int (2)) (Prims.of_int (150))
         (Prims.of_int (68)))
      (FStar_Tactics_Effect.lift_div_tac
         (fun uu___ ->
            (fun uu___ ->
               Obj.magic
                 (failwith "Cannot evaluate open quotation at runtime"))
              uu___))
      (fun uu___ ->
         (fun hd ->
            Obj.magic
              (FStar_Tactics_Effect.tac_bind
                 (FStar_Range.mk_range "FStar.Tactics.PatternMatching.fst"
                    (Prims.of_int (150)) (Prims.of_int (8))
                    (Prims.of_int (150)) (Prims.of_int (68)))
                 (FStar_Range.mk_range "FStar.Tactics.PatternMatching.fst"
                    (Prims.of_int (150)) (Prims.of_int (2))
                    (Prims.of_int (150)) (Prims.of_int (68)))
                 (Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Range.mk_range
                          "FStar.Tactics.PatternMatching.fst"
                          (Prims.of_int (150)) (Prims.of_int (19))
                          (Prims.of_int (150)) (Prims.of_int (67)))
                       (FStar_Range.mk_range
                          "FStar.Tactics.PatternMatching.fst"
                          (Prims.of_int (150)) (Prims.of_int (8))
                          (Prims.of_int (150)) (Prims.of_int (68)))
                       (Obj.magic
                          (FStar_Tactics_Effect.tac_bind
                             (FStar_Range.mk_range
                                "FStar.Tactics.PatternMatching.fst"
                                (Prims.of_int (150)) (Prims.of_int (20))
                                (Prims.of_int (150)) (Prims.of_int (66)))
                             (FStar_Range.mk_range
                                "FStar.Tactics.PatternMatching.fst"
                                (Prims.of_int (150)) (Prims.of_int (19))
                                (Prims.of_int (150)) (Prims.of_int (67)))
                             (Obj.magic
                                (FStar_Tactics_Effect.tac_bind
                                   (FStar_Range.mk_range
                                      "FStar.Tactics.PatternMatching.fst"
                                      (Prims.of_int (150))
                                      (Prims.of_int (21))
                                      (Prims.of_int (150))
                                      (Prims.of_int (53)))
                                   (FStar_Range.mk_range
                                      "FStar.Tactics.PatternMatching.fst"
                                      (Prims.of_int (150))
                                      (Prims.of_int (20))
                                      (Prims.of_int (150))
                                      (Prims.of_int (66)))
                                   (Obj.magic
                                      (FStar_Tactics_Builtins.pack
                                         (FStar_Reflection_Data.Tv_Var
                                            (FStar_Reflection_Derived.bv_of_binder
                                               h))))
                                   (fun uu___ ->
                                      FStar_Tactics_Effect.lift_div_tac
                                        (fun uu___1 ->
                                           (uu___,
                                             FStar_Reflection_Data.Q_Explicit)))))
                             (fun uu___ ->
                                FStar_Tactics_Effect.lift_div_tac
                                  (fun uu___1 -> [uu___]))))
                       (fun uu___ ->
                          FStar_Tactics_Effect.lift_div_tac
                            (fun uu___1 ->
                               FStar_Reflection_Derived.mk_app hd uu___))))
                 (fun uu___ ->
                    (fun uu___ ->
                       Obj.magic (FStar_Tactics_Derived.exact uu___)) uu___)))
           uu___)
let (exact_hyp' :
  FStar_Reflection_Types.binder -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun h ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Range.mk_range "FStar.Tactics.PatternMatching.fst"
         (Prims.of_int (154)) (Prims.of_int (8)) (Prims.of_int (154))
         (Prims.of_int (40)))
      (FStar_Range.mk_range "FStar.Tactics.PatternMatching.fst"
         (Prims.of_int (154)) (Prims.of_int (2)) (Prims.of_int (154))
         (Prims.of_int (40)))
      (Obj.magic
         (FStar_Tactics_Builtins.pack
            (FStar_Reflection_Data.Tv_Var
               (FStar_Reflection_Derived.bv_of_binder h))))
      (fun uu___ ->
         (fun uu___ -> Obj.magic (FStar_Tactics_Derived.exact uu___)) uu___)
type varname = Prims.string
type qn = Prims.string
type pattern =
  | PVar of varname 
  | PQn of qn 
  | PType 
  | PApp of pattern * pattern 
let (uu___is_PVar : pattern -> Prims.bool) =
  fun projectee -> match projectee with | PVar name -> true | uu___ -> false
let (__proj__PVar__item__name : pattern -> varname) =
  fun projectee -> match projectee with | PVar name -> name
let (uu___is_PQn : pattern -> Prims.bool) =
  fun projectee -> match projectee with | PQn qn1 -> true | uu___ -> false
let (__proj__PQn__item__qn : pattern -> qn) =
  fun projectee -> match projectee with | PQn qn1 -> qn1
let (uu___is_PType : pattern -> Prims.bool) =
  fun projectee -> match projectee with | PType -> true | uu___ -> false
let (uu___is_PApp : pattern -> Prims.bool) =
  fun projectee ->
    match projectee with | PApp (hd, arg) -> true | uu___ -> false
let (__proj__PApp__item__hd : pattern -> pattern) =
  fun projectee -> match projectee with | PApp (hd, arg) -> hd
let (__proj__PApp__item__arg : pattern -> pattern) =
  fun projectee -> match projectee with | PApp (hd, arg) -> arg
let (desc_of_pattern : pattern -> Prims.string) =
  fun uu___ ->
    match uu___ with
    | PVar uu___1 -> "a variable"
    | PQn qn1 -> Prims.strcat "a constant (" (Prims.strcat qn1 ")")
    | PType -> "Type"
    | PApp (uu___1, uu___2) -> "a function application"
let rec (string_of_pattern : pattern -> Prims.string) =
  fun uu___ ->
    match uu___ with
    | PVar x -> Prims.strcat "?" x
    | PQn qn1 -> qn1
    | PType -> "Type"
    | PApp (l, r) ->
        Prims.strcat "("
          (Prims.strcat (string_of_pattern l)
             (Prims.strcat " " (Prims.strcat (string_of_pattern r) ")")))
type match_exception =
  | NameMismatch of (qn * qn) 
  | SimpleMismatch of (pattern * FStar_Reflection_Types.term) 
  | NonLinearMismatch of (varname * FStar_Reflection_Types.term *
  FStar_Reflection_Types.term) 
  | UnsupportedTermInPattern of FStar_Reflection_Types.term 
  | IncorrectTypeInAbsPatBinder of FStar_Reflection_Types.typ 
let (uu___is_NameMismatch : match_exception -> Prims.bool) =
  fun projectee ->
    match projectee with | NameMismatch _0 -> true | uu___ -> false
let (__proj__NameMismatch__item___0 : match_exception -> (qn * qn)) =
  fun projectee -> match projectee with | NameMismatch _0 -> _0
let (uu___is_SimpleMismatch : match_exception -> Prims.bool) =
  fun projectee ->
    match projectee with | SimpleMismatch _0 -> true | uu___ -> false
let (__proj__SimpleMismatch__item___0 :
  match_exception -> (pattern * FStar_Reflection_Types.term)) =
  fun projectee -> match projectee with | SimpleMismatch _0 -> _0
let (uu___is_NonLinearMismatch : match_exception -> Prims.bool) =
  fun projectee ->
    match projectee with | NonLinearMismatch _0 -> true | uu___ -> false
let (__proj__NonLinearMismatch__item___0 :
  match_exception ->
    (varname * FStar_Reflection_Types.term * FStar_Reflection_Types.term))
  = fun projectee -> match projectee with | NonLinearMismatch _0 -> _0
let (uu___is_UnsupportedTermInPattern : match_exception -> Prims.bool) =
  fun projectee ->
    match projectee with
    | UnsupportedTermInPattern _0 -> true
    | uu___ -> false
let (__proj__UnsupportedTermInPattern__item___0 :
  match_exception -> FStar_Reflection_Types.term) =
  fun projectee -> match projectee with | UnsupportedTermInPattern _0 -> _0
let (uu___is_IncorrectTypeInAbsPatBinder : match_exception -> Prims.bool) =
  fun projectee ->
    match projectee with
    | IncorrectTypeInAbsPatBinder _0 -> true
    | uu___ -> false
let (__proj__IncorrectTypeInAbsPatBinder__item___0 :
  match_exception -> FStar_Reflection_Types.typ) =
  fun projectee ->
    match projectee with | IncorrectTypeInAbsPatBinder _0 -> _0
let (term_head :
  FStar_Reflection_Types.term ->
    (Prims.string, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Range.mk_range "FStar.Tactics.PatternMatching.fst"
         (Prims.of_int (203)) (Prims.of_int (8)) (Prims.of_int (203))
         (Prims.of_int (17)))
      (FStar_Range.mk_range "FStar.Tactics.PatternMatching.fst"
         (Prims.of_int (203)) (Prims.of_int (2)) (Prims.of_int (219))
         (Prims.of_int (30))) (Obj.magic (FStar_Tactics_Builtins.inspect t))
      (fun uu___ ->
         FStar_Tactics_Effect.lift_div_tac
           (fun uu___1 ->
              match uu___ with
              | FStar_Reflection_Data.Tv_Var bv -> "Tv_Var"
              | FStar_Reflection_Data.Tv_BVar fv -> "Tv_BVar"
              | FStar_Reflection_Data.Tv_FVar fv -> "Tv_FVar"
              | FStar_Reflection_Data.Tv_UInst (uu___2, uu___3) -> "Tv_UInst"
              | FStar_Reflection_Data.Tv_App (f, x) -> "Tv_App"
              | FStar_Reflection_Data.Tv_Abs (x, t1) -> "Tv_Abs"
              | FStar_Reflection_Data.Tv_Arrow (x, t1) -> "Tv_Arrow"
              | FStar_Reflection_Data.Tv_Type uu___2 -> "Tv_Type"
              | FStar_Reflection_Data.Tv_Refine (x, uu___2, t1) ->
                  "Tv_Refine"
              | FStar_Reflection_Data.Tv_Const cst -> "Tv_Const"
              | FStar_Reflection_Data.Tv_Uvar (i, t1) -> "Tv_Uvar"
              | FStar_Reflection_Data.Tv_Let (r, attrs, b, uu___2, t1, t2) ->
                  "Tv_Let"
              | FStar_Reflection_Data.Tv_Match (t1, uu___2, branches) ->
                  "Tv_Match"
              | FStar_Reflection_Data.Tv_AscribedT
                  (uu___2, uu___3, uu___4, uu___5) -> "Tv_AscribedT"
              | FStar_Reflection_Data.Tv_AscribedC
                  (uu___2, uu___3, uu___4, uu___5) -> "Tv_AscribedC"
              | FStar_Reflection_Data.Tv_Unknown -> "Tv_Unknown"))
let (string_of_match_exception :
  match_exception -> (Prims.string, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    (fun uu___ ->
       match uu___ with
       | NameMismatch (qn1, qn2) ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.lift_div_tac
                   (fun uu___1 ->
                      Prims.strcat
                        "Match failure (name mismatch): expecting "
                        (Prims.strcat qn1 (Prims.strcat ", found " qn2)))))
       | SimpleMismatch (pat, tm) ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Range.mk_range "FStar.Tactics.PatternMatching.fst"
                      (Prims.of_int (227)) (Prims.of_int (4))
                      (Prims.of_int (227)) (Prims.of_int (54)))
                   (FStar_Range.mk_range "prims.fst" (Prims.of_int (590))
                      (Prims.of_int (19)) (Prims.of_int (590))
                      (Prims.of_int (31)))
                   (Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (FStar_Range.mk_range
                            "FStar.Tactics.PatternMatching.fst"
                            (Prims.of_int (227)) (Prims.of_int (26))
                            (Prims.of_int (227)) (Prims.of_int (54)))
                         (FStar_Range.mk_range "prims.fst"
                            (Prims.of_int (590)) (Prims.of_int (19))
                            (Prims.of_int (590)) (Prims.of_int (31)))
                         (Obj.magic
                            (FStar_Tactics_Effect.tac_bind
                               (FStar_Range.mk_range
                                  "FStar.Tactics.PatternMatching.fst"
                                  (Prims.of_int (227)) (Prims.of_int (37))
                                  (Prims.of_int (227)) (Prims.of_int (54)))
                               (FStar_Range.mk_range "prims.fst"
                                  (Prims.of_int (590)) (Prims.of_int (19))
                                  (Prims.of_int (590)) (Prims.of_int (31)))
                               (Obj.magic
                                  (FStar_Tactics_Builtins.term_to_string tm))
                               (fun uu___1 ->
                                  FStar_Tactics_Effect.lift_div_tac
                                    (fun uu___2 ->
                                       Prims.strcat ", got " uu___1))))
                         (fun uu___1 ->
                            FStar_Tactics_Effect.lift_div_tac
                              (fun uu___2 ->
                                 Prims.strcat (desc_of_pattern pat) uu___1))))
                   (fun uu___1 ->
                      FStar_Tactics_Effect.lift_div_tac
                        (fun uu___2 ->
                           Prims.strcat
                             "Match failure (sort mismatch): expecting "
                             uu___1))))
       | NonLinearMismatch (nm, t1, t2) ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Range.mk_range "FStar.Tactics.PatternMatching.fst"
                      (Prims.of_int (229)) (Prims.of_int (54))
                      (Prims.of_int (231)) (Prims.of_int (33)))
                   (FStar_Range.mk_range "prims.fst" (Prims.of_int (590))
                      (Prims.of_int (19)) (Prims.of_int (590))
                      (Prims.of_int (31)))
                   (Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (FStar_Range.mk_range
                            "FStar.Tactics.PatternMatching.fst"
                            (Prims.of_int (230)) (Prims.of_int (4))
                            (Prims.of_int (231)) (Prims.of_int (33)))
                         (FStar_Range.mk_range "prims.fst"
                            (Prims.of_int (590)) (Prims.of_int (19))
                            (Prims.of_int (590)) (Prims.of_int (31)))
                         (Obj.magic
                            (FStar_Tactics_Effect.tac_bind
                               (FStar_Range.mk_range
                                  "FStar.Tactics.PatternMatching.fst"
                                  (Prims.of_int (230)) (Prims.of_int (30))
                                  (Prims.of_int (231)) (Prims.of_int (33)))
                               (FStar_Range.mk_range "prims.fst"
                                  (Prims.of_int (590)) (Prims.of_int (19))
                                  (Prims.of_int (590)) (Prims.of_int (31)))
                               (Obj.magic
                                  (FStar_Tactics_Effect.tac_bind
                                     (FStar_Range.mk_range
                                        "FStar.Tactics.PatternMatching.fst"
                                        (Prims.of_int (230))
                                        (Prims.of_int (30))
                                        (Prims.of_int (230))
                                        (Prims.of_int (49)))
                                     (FStar_Range.mk_range
                                        "FStar.Tactics.PatternMatching.fst"
                                        (Prims.of_int (230))
                                        (Prims.of_int (30))
                                        (Prims.of_int (231))
                                        (Prims.of_int (33)))
                                     (Obj.magic
                                        (FStar_Tactics_Builtins.term_to_string
                                           t1))
                                     (fun uu___1 ->
                                        (fun uu___1 ->
                                           Obj.magic
                                             (FStar_Tactics_Effect.tac_bind
                                                (FStar_Range.mk_range
                                                   "FStar.Tactics.PatternMatching.fst"
                                                   (Prims.of_int (231))
                                                   (Prims.of_int (4))
                                                   (Prims.of_int (231))
                                                   (Prims.of_int (33)))
                                                (FStar_Range.mk_range
                                                   "prims.fst"
                                                   (Prims.of_int (590))
                                                   (Prims.of_int (19))
                                                   (Prims.of_int (590))
                                                   (Prims.of_int (31)))
                                                (Obj.magic
                                                   (FStar_Tactics_Effect.tac_bind
                                                      (FStar_Range.mk_range
                                                         "FStar.Tactics.PatternMatching.fst"
                                                         (Prims.of_int (231))
                                                         (Prims.of_int (14))
                                                         (Prims.of_int (231))
                                                         (Prims.of_int (33)))
                                                      (FStar_Range.mk_range
                                                         "prims.fst"
                                                         (Prims.of_int (590))
                                                         (Prims.of_int (19))
                                                         (Prims.of_int (590))
                                                         (Prims.of_int (31)))
                                                      (Obj.magic
                                                         (FStar_Tactics_Builtins.term_to_string
                                                            t2))
                                                      (fun uu___2 ->
                                                         FStar_Tactics_Effect.lift_div_tac
                                                           (fun uu___3 ->
                                                              Prims.strcat
                                                                " and "
                                                                uu___2))))
                                                (fun uu___2 ->
                                                   FStar_Tactics_Effect.lift_div_tac
                                                     (fun uu___3 ->
                                                        Prims.strcat uu___1
                                                          uu___2)))) uu___1)))
                               (fun uu___1 ->
                                  FStar_Tactics_Effect.lift_div_tac
                                    (fun uu___2 ->
                                       Prims.strcat " needs to match both "
                                         uu___1))))
                         (fun uu___1 ->
                            FStar_Tactics_Effect.lift_div_tac
                              (fun uu___2 -> Prims.strcat nm uu___1))))
                   (fun uu___1 ->
                      FStar_Tactics_Effect.lift_div_tac
                        (fun uu___2 ->
                           Prims.strcat
                             "Match failure (nonlinear mismatch): variable "
                             uu___1))))
       | UnsupportedTermInPattern tm ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Range.mk_range "FStar.Tactics.PatternMatching.fst"
                      (Prims.of_int (234)) (Prims.of_int (4))
                      (Prims.of_int (234)) (Prims.of_int (49)))
                   (FStar_Range.mk_range "prims.fst" (Prims.of_int (590))
                      (Prims.of_int (19)) (Prims.of_int (590))
                      (Prims.of_int (31)))
                   (Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (FStar_Range.mk_range
                            "FStar.Tactics.PatternMatching.fst"
                            (Prims.of_int (234)) (Prims.of_int (4))
                            (Prims.of_int (234)) (Prims.of_int (21)))
                         (FStar_Range.mk_range
                            "FStar.Tactics.PatternMatching.fst"
                            (Prims.of_int (234)) (Prims.of_int (4))
                            (Prims.of_int (234)) (Prims.of_int (49)))
                         (Obj.magic
                            (FStar_Tactics_Builtins.term_to_string tm))
                         (fun uu___1 ->
                            (fun uu___1 ->
                               Obj.magic
                                 (FStar_Tactics_Effect.tac_bind
                                    (FStar_Range.mk_range
                                       "FStar.Tactics.PatternMatching.fst"
                                       (Prims.of_int (234))
                                       (Prims.of_int (24))
                                       (Prims.of_int (234))
                                       (Prims.of_int (49)))
                                    (FStar_Range.mk_range "prims.fst"
                                       (Prims.of_int (590))
                                       (Prims.of_int (19))
                                       (Prims.of_int (590))
                                       (Prims.of_int (31)))
                                    (Obj.magic
                                       (FStar_Tactics_Effect.tac_bind
                                          (FStar_Range.mk_range
                                             "FStar.Tactics.PatternMatching.fst"
                                             (Prims.of_int (234))
                                             (Prims.of_int (31))
                                             (Prims.of_int (234))
                                             (Prims.of_int (49)))
                                          (FStar_Range.mk_range "prims.fst"
                                             (Prims.of_int (590))
                                             (Prims.of_int (19))
                                             (Prims.of_int (590))
                                             (Prims.of_int (31)))
                                          (Obj.magic
                                             (FStar_Tactics_Effect.tac_bind
                                                (FStar_Range.mk_range
                                                   "FStar.Tactics.PatternMatching.fst"
                                                   (Prims.of_int (234))
                                                   (Prims.of_int (31))
                                                   (Prims.of_int (234))
                                                   (Prims.of_int (43)))
                                                (FStar_Range.mk_range
                                                   "prims.fst"
                                                   (Prims.of_int (590))
                                                   (Prims.of_int (19))
                                                   (Prims.of_int (590))
                                                   (Prims.of_int (31)))
                                                (Obj.magic (term_head tm))
                                                (fun uu___2 ->
                                                   FStar_Tactics_Effect.lift_div_tac
                                                     (fun uu___3 ->
                                                        Prims.strcat uu___2
                                                          ")"))))
                                          (fun uu___2 ->
                                             FStar_Tactics_Effect.lift_div_tac
                                               (fun uu___3 ->
                                                  Prims.strcat " (" uu___2))))
                                    (fun uu___2 ->
                                       FStar_Tactics_Effect.lift_div_tac
                                         (fun uu___3 ->
                                            Prims.strcat uu___1 uu___2))))
                              uu___1)))
                   (fun uu___1 ->
                      FStar_Tactics_Effect.lift_div_tac
                        (fun uu___2 ->
                           Prims.strcat
                             "Match failure (unsupported term in pattern): "
                             uu___1))))
       | IncorrectTypeInAbsPatBinder typ ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Range.mk_range "FStar.Tactics.PatternMatching.fst"
                      (Prims.of_int (237)) (Prims.of_int (4))
                      (Prims.of_int (237)) (Prims.of_int (74)))
                   (FStar_Range.mk_range "prims.fst" (Prims.of_int (590))
                      (Prims.of_int (19)) (Prims.of_int (590))
                      (Prims.of_int (31)))
                   (Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (FStar_Range.mk_range
                            "FStar.Tactics.PatternMatching.fst"
                            (Prims.of_int (237)) (Prims.of_int (4))
                            (Prims.of_int (237)) (Prims.of_int (22)))
                         (FStar_Range.mk_range "prims.fst"
                            (Prims.of_int (590)) (Prims.of_int (19))
                            (Prims.of_int (590)) (Prims.of_int (31)))
                         (Obj.magic
                            (FStar_Tactics_Builtins.term_to_string typ))
                         (fun uu___1 ->
                            FStar_Tactics_Effect.lift_div_tac
                              (fun uu___2 ->
                                 Prims.strcat uu___1
                                   " (use one of ``var``, ``hyp \226\128\166``, or ``goal \226\128\166``)"))))
                   (fun uu___1 ->
                      FStar_Tactics_Effect.lift_div_tac
                        (fun uu___2 ->
                           Prims.strcat
                             "Incorrect type in pattern-matching binder: "
                             uu___1))))) uu___
type 'a match_res =
  | Success of 'a 
  | Failure of match_exception 
let uu___is_Success : 'a . 'a match_res -> Prims.bool =
  fun projectee -> match projectee with | Success _0 -> true | uu___ -> false
let __proj__Success__item___0 : 'a . 'a match_res -> 'a =
  fun projectee -> match projectee with | Success _0 -> _0
let uu___is_Failure : 'a . 'a match_res -> Prims.bool =
  fun projectee -> match projectee with | Failure _0 -> true | uu___ -> false
let __proj__Failure__item___0 : 'a . 'a match_res -> match_exception =
  fun projectee -> match projectee with | Failure _0 -> _0
let return : 'a . 'a -> 'a match_res = fun x -> Success x
let op_let_Question :
  'a 'b .
    'a match_res ->
      ('a -> ('b match_res, unit) FStar_Tactics_Effect.tac_repr) ->
        ('b match_res, unit) FStar_Tactics_Effect.tac_repr
  =
  fun uu___1 ->
    fun uu___ ->
      (fun f ->
         fun g ->
           match f with
           | Success aa -> Obj.magic (Obj.repr (g aa))
           | Failure ex ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.lift_div_tac
                       (fun uu___ -> Failure ex)))) uu___1 uu___
let raise : 'a . match_exception -> 'a match_res = fun ex -> Failure ex
let lift_exn_tac :
  'a 'b .
    ('a -> 'b match_res) -> 'a -> ('b, unit) FStar_Tactics_Effect.tac_repr
  =
  fun uu___1 ->
    fun uu___ ->
      (fun f ->
         fun aa ->
           match f aa with
           | Success bb ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> bb)))
           | Failure ex ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Range.mk_range
                          "FStar.Tactics.PatternMatching.fst"
                          (Prims.of_int (268)) (Prims.of_int (31))
                          (Prims.of_int (268)) (Prims.of_int (61)))
                       (FStar_Range.mk_range
                          "FStar.Tactics.PatternMatching.fst"
                          (Prims.of_int (268)) (Prims.of_int (18))
                          (Prims.of_int (268)) (Prims.of_int (61)))
                       (Obj.magic (string_of_match_exception ex))
                       (fun uu___ -> FStar_Tactics_Derived.fail uu___))))
        uu___1 uu___
let lift_exn_tactic :
  'a 'b .
    ('a -> 'b match_res) -> 'a -> ('b, unit) FStar_Tactics_Effect.tac_repr
  =
  fun uu___1 ->
    fun uu___ ->
      (fun f ->
         fun aa ->
           match f aa with
           | Success bb ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> bb)))
           | Failure ex ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Range.mk_range
                          "FStar.Tactics.PatternMatching.fst"
                          (Prims.of_int (273)) (Prims.of_int (31))
                          (Prims.of_int (273)) (Prims.of_int (61)))
                       (FStar_Range.mk_range
                          "FStar.Tactics.PatternMatching.fst"
                          (Prims.of_int (273)) (Prims.of_int (18))
                          (Prims.of_int (273)) (Prims.of_int (61)))
                       (Obj.magic (string_of_match_exception ex))
                       (fun uu___ -> FStar_Tactics_Derived.fail uu___))))
        uu___1 uu___
type bindings = (varname * FStar_Reflection_Types.term) Prims.list
let (string_of_bindings :
  bindings -> (Prims.string, unit) FStar_Tactics_Effect.tac_repr) =
  fun bindings1 ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Range.mk_range "FStar.Tactics.PatternMatching.fst"
         (Prims.of_int (285)) (Prims.of_int (4)) (Prims.of_int (286))
         (Prims.of_int (27)))
      (FStar_Range.mk_range "FStar.Tactics.PatternMatching.fst"
         (Prims.of_int (284)) (Prims.of_int (2)) (Prims.of_int (286))
         (Prims.of_int (27)))
      (Obj.magic
         (FStar_Tactics_Util.map
            (fun uu___ ->
               match uu___ with
               | (nm, tm) ->
                   FStar_Tactics_Effect.tac_bind
                     (FStar_Range.mk_range
                        "FStar.Tactics.PatternMatching.fst"
                        (Prims.of_int (285)) (Prims.of_int (35))
                        (Prims.of_int (285)) (Prims.of_int (64)))
                     (FStar_Range.mk_range "prims.fst" (Prims.of_int (590))
                        (Prims.of_int (19)) (Prims.of_int (590))
                        (Prims.of_int (31)))
                     (Obj.magic
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Range.mk_range
                              "FStar.Tactics.PatternMatching.fst"
                              (Prims.of_int (285)) (Prims.of_int (40))
                              (Prims.of_int (285)) (Prims.of_int (64)))
                           (FStar_Range.mk_range "prims.fst"
                              (Prims.of_int (590)) (Prims.of_int (19))
                              (Prims.of_int (590)) (Prims.of_int (31)))
                           (Obj.magic
                              (FStar_Tactics_Effect.tac_bind
                                 (FStar_Range.mk_range
                                    "FStar.Tactics.PatternMatching.fst"
                                    (Prims.of_int (285)) (Prims.of_int (47))
                                    (Prims.of_int (285)) (Prims.of_int (64)))
                                 (FStar_Range.mk_range "prims.fst"
                                    (Prims.of_int (590)) (Prims.of_int (19))
                                    (Prims.of_int (590)) (Prims.of_int (31)))
                                 (Obj.magic
                                    (FStar_Tactics_Builtins.term_to_string tm))
                                 (fun uu___1 ->
                                    FStar_Tactics_Effect.lift_div_tac
                                      (fun uu___2 -> Prims.strcat ": " uu___1))))
                           (fun uu___1 ->
                              FStar_Tactics_Effect.lift_div_tac
                                (fun uu___2 -> Prims.strcat nm uu___1))))
                     (fun uu___1 ->
                        FStar_Tactics_Effect.lift_div_tac
                          (fun uu___2 -> Prims.strcat ">> " uu___1)))
            bindings1))
      (fun uu___ ->
         FStar_Tactics_Effect.lift_div_tac
           (fun uu___1 -> FStar_String.concat "\n" uu___))
let rec (interp_pattern_aux :
  pattern ->
    bindings ->
      FStar_Reflection_Types.term ->
        (bindings match_res, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun pat ->
    fun cur_bindings ->
      fun tm ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Range.mk_range "FStar.Tactics.PatternMatching.fst"
             (Prims.of_int (294)) (Prims.of_int (4)) (Prims.of_int (297))
             (Prims.of_int (46)))
          (FStar_Range.mk_range "FStar.Tactics.PatternMatching.fst"
             (Prims.of_int (297)) (Prims.of_int (49)) (Prims.of_int (304))
             (Prims.of_int (46)))
          (FStar_Tactics_Effect.lift_div_tac
             (fun uu___ ->
                fun v ->
                  fun cur_bindings1 ->
                    fun tm1 ->
                      match FStar_List_Tot_Base.assoc v cur_bindings1 with
                      | FStar_Pervasives_Native.Some tm' ->
                          if FStar_Reflection_Builtins.term_eq tm1 tm'
                          then return cur_bindings1
                          else raise (NonLinearMismatch (v, tm1, tm'))
                      | FStar_Pervasives_Native.None ->
                          return ((v, tm1) :: cur_bindings1)))
          (fun uu___ ->
             (fun interp_var ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Range.mk_range
                        "FStar.Tactics.PatternMatching.fst"
                        (Prims.of_int (299)) (Prims.of_int (4))
                        (Prims.of_int (304)) (Prims.of_int (43)))
                     (FStar_Range.mk_range
                        "FStar.Tactics.PatternMatching.fst"
                        (Prims.of_int (304)) (Prims.of_int (46))
                        (Prims.of_int (308)) (Prims.of_int (46)))
                     (FStar_Tactics_Effect.lift_div_tac
                        (fun uu___ ->
                           fun qn1 ->
                             fun cur_bindings1 ->
                               fun tm1 ->
                                 FStar_Tactics_Effect.tac_bind
                                   (FStar_Range.mk_range
                                      "FStar.Tactics.PatternMatching.fst"
                                      (Prims.of_int (299))
                                      (Prims.of_int (10))
                                      (Prims.of_int (299))
                                      (Prims.of_int (20)))
                                   (FStar_Range.mk_range
                                      "FStar.Tactics.PatternMatching.fst"
                                      (Prims.of_int (299)) (Prims.of_int (4))
                                      (Prims.of_int (304))
                                      (Prims.of_int (43)))
                                   (Obj.magic
                                      (FStar_Tactics_Builtins.inspect tm1))
                                   (fun uu___1 ->
                                      FStar_Tactics_Effect.lift_div_tac
                                        (fun uu___2 ->
                                           match uu___1 with
                                           | FStar_Reflection_Data.Tv_UInst
                                               (fv, uu___3) ->
                                               if
                                                 (FStar_Reflection_Derived.fv_to_string
                                                    fv)
                                                   = qn1
                                               then return cur_bindings1
                                               else
                                                 raise
                                                   (NameMismatch
                                                      (qn1,
                                                        (FStar_Reflection_Derived.fv_to_string
                                                           fv)))
                                           | FStar_Reflection_Data.Tv_FVar fv
                                               ->
                                               if
                                                 (FStar_Reflection_Derived.fv_to_string
                                                    fv)
                                                   = qn1
                                               then return cur_bindings1
                                               else
                                                 raise
                                                   (NameMismatch
                                                      (qn1,
                                                        (FStar_Reflection_Derived.fv_to_string
                                                           fv)))
                                           | uu___3 ->
                                               raise
                                                 (SimpleMismatch (pat, tm1))))))
                     (fun uu___ ->
                        (fun interp_qn ->
                           Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Range.mk_range
                                   "FStar.Tactics.PatternMatching.fst"
                                   (Prims.of_int (306)) (Prims.of_int (4))
                                   (Prims.of_int (308)) (Prims.of_int (43)))
                                (FStar_Range.mk_range
                                   "FStar.Tactics.PatternMatching.fst"
                                   (Prims.of_int (308)) (Prims.of_int (46))
                                   (Prims.of_int (315)) (Prims.of_int (46)))
                                (FStar_Tactics_Effect.lift_div_tac
                                   (fun uu___ ->
                                      fun cur_bindings1 ->
                                        fun tm1 ->
                                          FStar_Tactics_Effect.tac_bind
                                            (FStar_Range.mk_range
                                               "FStar.Tactics.PatternMatching.fst"
                                               (Prims.of_int (306))
                                               (Prims.of_int (10))
                                               (Prims.of_int (306))
                                               (Prims.of_int (20)))
                                            (FStar_Range.mk_range
                                               "FStar.Tactics.PatternMatching.fst"
                                               (Prims.of_int (306))
                                               (Prims.of_int (4))
                                               (Prims.of_int (308))
                                               (Prims.of_int (43)))
                                            (Obj.magic
                                               (FStar_Tactics_Builtins.inspect
                                                  tm1))
                                            (fun uu___1 ->
                                               FStar_Tactics_Effect.lift_div_tac
                                                 (fun uu___2 ->
                                                    match uu___1 with
                                                    | FStar_Reflection_Data.Tv_Type
                                                        uu___3 ->
                                                        return cur_bindings1
                                                    | uu___3 ->
                                                        raise
                                                          (SimpleMismatch
                                                             (pat, tm1))))))
                                (fun uu___ ->
                                   (fun interp_type ->
                                      Obj.magic
                                        (FStar_Tactics_Effect.tac_bind
                                           (FStar_Range.mk_range
                                              "FStar.Tactics.PatternMatching.fst"
                                              (Prims.of_int (310))
                                              (Prims.of_int (4))
                                              (Prims.of_int (315))
                                              (Prims.of_int (43)))
                                           (FStar_Range.mk_range
                                              "FStar.Tactics.PatternMatching.fst"
                                              (Prims.of_int (316))
                                              (Prims.of_int (4))
                                              (Prims.of_int (323))
                                              (Prims.of_int (19)))
                                           (FStar_Tactics_Effect.lift_div_tac
                                              (fun uu___ ->
                                                 fun p_hd ->
                                                   fun p_arg ->
                                                     fun cur_bindings1 ->
                                                       fun tm1 ->
                                                         FStar_Tactics_Effect.tac_bind
                                                           (FStar_Range.mk_range
                                                              "FStar.Tactics.PatternMatching.fst"
                                                              (Prims.of_int (310))
                                                              (Prims.of_int (10))
                                                              (Prims.of_int (310))
                                                              (Prims.of_int (20)))
                                                           (FStar_Range.mk_range
                                                              "FStar.Tactics.PatternMatching.fst"
                                                              (Prims.of_int (310))
                                                              (Prims.of_int (4))
                                                              (Prims.of_int (315))
                                                              (Prims.of_int (43)))
                                                           (Obj.magic
                                                              (FStar_Tactics_Builtins.inspect
                                                                 tm1))
                                                           (fun uu___1 ->
                                                              (fun uu___1 ->
                                                                 match uu___1
                                                                 with
                                                                 | FStar_Reflection_Data.Tv_App
                                                                    (hd,
                                                                    (arg,
                                                                    uu___2))
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (312))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (312))
                                                                    (Prims.of_int (60)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (312))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (314))
                                                                    (Prims.of_int (21)))
                                                                    (Obj.magic
                                                                    (interp_pattern_aux
                                                                    p_hd
                                                                    cur_bindings1
                                                                    hd))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    Obj.magic
                                                                    (op_let_Question
                                                                    uu___3
                                                                    (fun
                                                                    with_hd
                                                                    ->
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (313))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (313))
                                                                    (Prims.of_int (58)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (313))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (314))
                                                                    (Prims.of_int (21)))
                                                                    (Obj.magic
                                                                    (interp_pattern_aux
                                                                    p_arg
                                                                    with_hd
                                                                    arg))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    Obj.magic
                                                                    (op_let_Question
                                                                    uu___4
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    with_arg
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    return
                                                                    with_arg)))
                                                                    uu___5)))
                                                                    uu___4))))
                                                                    uu___3)))
                                                                 | uu___2 ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    raise
                                                                    (SimpleMismatch
                                                                    (pat,
                                                                    tm1))))))
                                                                uu___1)))
                                           (fun uu___ ->
                                              (fun interp_app ->
                                                 match pat with
                                                 | PVar var ->
                                                     Obj.magic
                                                       (Obj.repr
                                                          (FStar_Tactics_Effect.lift_div_tac
                                                             (fun uu___ ->
                                                                interp_var
                                                                  var
                                                                  cur_bindings
                                                                  tm)))
                                                 | PQn qn1 ->
                                                     Obj.magic
                                                       (Obj.repr
                                                          (interp_qn qn1
                                                             cur_bindings tm))
                                                 | PType ->
                                                     Obj.magic
                                                       (Obj.repr
                                                          (interp_type
                                                             cur_bindings tm))
                                                 | PApp (p_hd, p_arg) ->
                                                     Obj.magic
                                                       (Obj.repr
                                                          (interp_app p_hd
                                                             p_arg
                                                             cur_bindings tm))
                                                 | uu___ ->
                                                     Obj.magic
                                                       (Obj.repr
                                                          (FStar_Tactics_Derived.fail
                                                             "?"))) uu___)))
                                     uu___))) uu___))) uu___)
let (interp_pattern :
  pattern ->
    FStar_Reflection_Types.term ->
      (bindings match_res, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun pat ->
    fun tm ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Range.mk_range "FStar.Tactics.PatternMatching.fst"
           (Prims.of_int (329)) (Prims.of_int (24)) (Prims.of_int (329))
           (Prims.of_int (52)))
        (FStar_Range.mk_range "FStar.Tactics.PatternMatching.fst"
           (Prims.of_int (329)) (Prims.of_int (4)) (Prims.of_int (330))
           (Prims.of_int (43))) (Obj.magic (interp_pattern_aux pat [] tm))
        (fun uu___ ->
           (fun uu___ ->
              Obj.magic
                (op_let_Question uu___
                   (fun uu___1 ->
                      (fun rev_bindings ->
                         Obj.magic
                           (FStar_Tactics_Effect.lift_div_tac
                              (fun uu___1 ->
                                 return
                                   (FStar_List_Tot_Base.rev rev_bindings))))
                        uu___1))) uu___)
let (match_term :
  pattern ->
    FStar_Reflection_Types.term ->
      (bindings, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun pat ->
    fun tm ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Range.mk_range "FStar.Tactics.PatternMatching.fst"
           (Prims.of_int (336)) (Prims.of_int (10)) (Prims.of_int (336))
           (Prims.of_int (46)))
        (FStar_Range.mk_range "FStar.Tactics.PatternMatching.fst"
           (Prims.of_int (336)) (Prims.of_int (4)) (Prims.of_int (338))
           (Prims.of_int (63)))
        (Obj.magic
           (FStar_Tactics_Effect.tac_bind
              (FStar_Range.mk_range "FStar.Tactics.PatternMatching.fst"
                 (Prims.of_int (336)) (Prims.of_int (29))
                 (Prims.of_int (336)) (Prims.of_int (46)))
              (FStar_Range.mk_range "FStar.Tactics.PatternMatching.fst"
                 (Prims.of_int (336)) (Prims.of_int (10))
                 (Prims.of_int (336)) (Prims.of_int (46)))
              (Obj.magic (FStar_Tactics_Derived.norm_term [] tm))
              (fun uu___ ->
                 (fun uu___ -> Obj.magic (interp_pattern pat uu___)) uu___)))
        (fun uu___ ->
           (fun uu___ ->
              match uu___ with
              | Success bb ->
                  Obj.magic
                    (Obj.repr
                       (FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> bb)))
              | Failure ex ->
                  Obj.magic
                    (Obj.repr
                       (FStar_Tactics_Effect.tac_bind
                          (FStar_Range.mk_range
                             "FStar.Tactics.PatternMatching.fst"
                             (Prims.of_int (338)) (Prims.of_int (33))
                             (Prims.of_int (338)) (Prims.of_int (63)))
                          (FStar_Range.mk_range
                             "FStar.Tactics.PatternMatching.fst"
                             (Prims.of_int (338)) (Prims.of_int (20))
                             (Prims.of_int (338)) (Prims.of_int (63)))
                          (Obj.magic (string_of_match_exception ex))
                          (fun uu___1 -> FStar_Tactics_Derived.fail uu___1))))
             uu___)
let debug : 'uuuuu . 'uuuuu -> (unit, unit) FStar_Tactics_Effect.tac_repr =
  fun uu___ ->
    (fun msg ->
       Obj.magic (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> ()))) uu___
type absvar = FStar_Reflection_Types.binder
type hypothesis = FStar_Reflection_Types.binder
type matching_problem =
  {
  mp_vars: varname Prims.list ;
  mp_hyps: (varname * pattern) Prims.list ;
  mp_goal: pattern FStar_Pervasives_Native.option }
let (__proj__Mkmatching_problem__item__mp_vars :
  matching_problem -> varname Prims.list) =
  fun projectee ->
    match projectee with | { mp_vars; mp_hyps; mp_goal;_} -> mp_vars
let (__proj__Mkmatching_problem__item__mp_hyps :
  matching_problem -> (varname * pattern) Prims.list) =
  fun projectee ->
    match projectee with | { mp_vars; mp_hyps; mp_goal;_} -> mp_hyps
let (__proj__Mkmatching_problem__item__mp_goal :
  matching_problem -> pattern FStar_Pervasives_Native.option) =
  fun projectee ->
    match projectee with | { mp_vars; mp_hyps; mp_goal;_} -> mp_goal
let (string_of_matching_problem : matching_problem -> Prims.string) =
  fun mp ->
    let vars = FStar_String.concat ", " mp.mp_vars in
    let hyps =
      FStar_String.concat "\n        "
        (FStar_List_Tot_Base.map
           (fun uu___ ->
              match uu___ with
              | (nm, pat) ->
                  Prims.strcat nm (Prims.strcat ": " (string_of_pattern pat)))
           mp.mp_hyps) in
    let goal =
      match mp.mp_goal with
      | FStar_Pervasives_Native.None -> "_"
      | FStar_Pervasives_Native.Some pat -> string_of_pattern pat in
    Prims.strcat "\n{ vars: "
      (Prims.strcat vars
         (Prims.strcat "\n"
            (Prims.strcat "  hyps: "
               (Prims.strcat hyps
                  (Prims.strcat "\n"
                     (Prims.strcat "  goal: " (Prims.strcat goal " }")))))))
type matching_solution =
  {
  ms_vars: (varname * FStar_Reflection_Types.term) Prims.list ;
  ms_hyps: (varname * hypothesis) Prims.list }
let (__proj__Mkmatching_solution__item__ms_vars :
  matching_solution -> (varname * FStar_Reflection_Types.term) Prims.list) =
  fun projectee -> match projectee with | { ms_vars; ms_hyps;_} -> ms_vars
let (__proj__Mkmatching_solution__item__ms_hyps :
  matching_solution -> (varname * hypothesis) Prims.list) =
  fun projectee -> match projectee with | { ms_vars; ms_hyps;_} -> ms_hyps
let (string_of_matching_solution :
  matching_solution -> (Prims.string, unit) FStar_Tactics_Effect.tac_repr) =
  fun ms ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Range.mk_range "FStar.Tactics.PatternMatching.fst"
         (Prims.of_int (385)) (Prims.of_int (4)) (Prims.of_int (387))
         (Prims.of_int (57)))
      (FStar_Range.mk_range "FStar.Tactics.PatternMatching.fst"
         (Prims.of_int (387)) (Prims.of_int (60)) (Prims.of_int (391))
         (Prims.of_int (61)))
      (Obj.magic
         (FStar_Tactics_Effect.tac_bind
            (FStar_Range.mk_range "FStar.Tactics.PatternMatching.fst"
               (Prims.of_int (386)) (Prims.of_int (6)) (Prims.of_int (387))
               (Prims.of_int (57)))
            (FStar_Range.mk_range "FStar.Tactics.PatternMatching.fst"
               (Prims.of_int (385)) (Prims.of_int (4)) (Prims.of_int (387))
               (Prims.of_int (57)))
            (Obj.magic
               (FStar_Tactics_Util.map
                  (fun uu___ ->
                     match uu___ with
                     | (varname1, tm) ->
                         FStar_Tactics_Effect.tac_bind
                           (FStar_Range.mk_range
                              "FStar.Tactics.PatternMatching.fst"
                              (Prims.of_int (387)) (Prims.of_int (18))
                              (Prims.of_int (387)) (Prims.of_int (44)))
                           (FStar_Range.mk_range "prims.fst"
                              (Prims.of_int (590)) (Prims.of_int (19))
                              (Prims.of_int (590)) (Prims.of_int (31)))
                           (Obj.magic
                              (FStar_Tactics_Effect.tac_bind
                                 (FStar_Range.mk_range
                                    "FStar.Tactics.PatternMatching.fst"
                                    (Prims.of_int (387)) (Prims.of_int (25))
                                    (Prims.of_int (387)) (Prims.of_int (44)))
                                 (FStar_Range.mk_range "prims.fst"
                                    (Prims.of_int (590)) (Prims.of_int (19))
                                    (Prims.of_int (590)) (Prims.of_int (31)))
                                 (Obj.magic
                                    (FStar_Tactics_Builtins.term_to_string tm))
                                 (fun uu___1 ->
                                    FStar_Tactics_Effect.lift_div_tac
                                      (fun uu___2 -> Prims.strcat ": " uu___1))))
                           (fun uu___1 ->
                              FStar_Tactics_Effect.lift_div_tac
                                (fun uu___2 -> Prims.strcat varname1 uu___1)))
                  ms.ms_vars))
            (fun uu___ ->
               FStar_Tactics_Effect.lift_div_tac
                 (fun uu___1 -> FStar_String.concat "\n            " uu___))))
      (fun uu___ ->
         (fun vars ->
            Obj.magic
              (FStar_Tactics_Effect.tac_bind
                 (FStar_Range.mk_range "FStar.Tactics.PatternMatching.fst"
                    (Prims.of_int (389)) (Prims.of_int (4))
                    (Prims.of_int (391)) (Prims.of_int (58)))
                 (FStar_Range.mk_range "prims.fst" (Prims.of_int (590))
                    (Prims.of_int (19)) (Prims.of_int (590))
                    (Prims.of_int (31)))
                 (Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Range.mk_range
                          "FStar.Tactics.PatternMatching.fst"
                          (Prims.of_int (390)) (Prims.of_int (6))
                          (Prims.of_int (391)) (Prims.of_int (58)))
                       (FStar_Range.mk_range
                          "FStar.Tactics.PatternMatching.fst"
                          (Prims.of_int (389)) (Prims.of_int (4))
                          (Prims.of_int (391)) (Prims.of_int (58)))
                       (Obj.magic
                          (FStar_Tactics_Util.map
                             (fun uu___ ->
                                match uu___ with
                                | (nm, binder) ->
                                    FStar_Tactics_Effect.tac_bind
                                      (FStar_Range.mk_range
                                         "FStar.Tactics.PatternMatching.fst"
                                         (Prims.of_int (391))
                                         (Prims.of_int (13))
                                         (Prims.of_int (391))
                                         (Prims.of_int (45)))
                                      (FStar_Range.mk_range "prims.fst"
                                         (Prims.of_int (590))
                                         (Prims.of_int (19))
                                         (Prims.of_int (590))
                                         (Prims.of_int (31)))
                                      (Obj.magic
                                         (FStar_Tactics_Effect.tac_bind
                                            (FStar_Range.mk_range
                                               "FStar.Tactics.PatternMatching.fst"
                                               (Prims.of_int (391))
                                               (Prims.of_int (20))
                                               (Prims.of_int (391))
                                               (Prims.of_int (45)))
                                            (FStar_Range.mk_range "prims.fst"
                                               (Prims.of_int (590))
                                               (Prims.of_int (19))
                                               (Prims.of_int (590))
                                               (Prims.of_int (31)))
                                            (Obj.magic
                                               (FStar_Tactics_Derived.binder_to_string
                                                  binder))
                                            (fun uu___1 ->
                                               FStar_Tactics_Effect.lift_div_tac
                                                 (fun uu___2 ->
                                                    Prims.strcat ": " uu___1))))
                                      (fun uu___1 ->
                                         FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___2 ->
                                              Prims.strcat nm uu___1)))
                             ms.ms_hyps))
                       (fun uu___ ->
                          FStar_Tactics_Effect.lift_div_tac
                            (fun uu___1 ->
                               FStar_String.concat "\n        " uu___))))
                 (fun hyps ->
                    FStar_Tactics_Effect.lift_div_tac
                      (fun uu___ ->
                         Prims.strcat "\n{ vars: "
                           (Prims.strcat vars
                              (Prims.strcat "\n"
                                 (Prims.strcat "  hyps: "
                                    (Prims.strcat hyps " }")))))))) uu___)
let assoc_varname_fail :
  'b .
    varname ->
      (varname * 'b) Prims.list -> ('b, unit) FStar_Tactics_Effect.tac_repr
  =
  fun uu___1 ->
    fun uu___ ->
      (fun key ->
         fun ls ->
           match FStar_List_Tot_Base.assoc key ls with
           | FStar_Pervasives_Native.None ->
               Obj.magic
                 (FStar_Tactics_Derived.fail (Prims.strcat "Not found: " key))
           | FStar_Pervasives_Native.Some x ->
               Obj.magic (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> x)))
        uu___1 uu___
let ms_locate_hyp :
  'a .
    matching_solution ->
      varname ->
        (FStar_Reflection_Types.binder, unit) FStar_Tactics_Effect.tac_repr
  = fun solution -> fun name -> assoc_varname_fail name solution.ms_hyps
let ms_locate_var :
  'a .
    matching_solution -> varname -> ('a, unit) FStar_Tactics_Effect.tac_repr
  =
  fun solution ->
    fun name ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Range.mk_range "FStar.Tactics.PatternMatching.fst"
           (Prims.of_int (408)) (Prims.of_int (13)) (Prims.of_int (408))
           (Prims.of_int (55)))
        (FStar_Range.mk_range "FStar.Tactics.PatternMatching.fst"
           (Prims.of_int (408)) (Prims.of_int (2)) (Prims.of_int (408))
           (Prims.of_int (55)))
        (Obj.magic (assoc_varname_fail name solution.ms_vars))
        (fun uu___ ->
           (fun uu___ -> Obj.magic (FStar_Tactics_Builtins.unquote uu___))
             uu___)
let ms_locate_unit :
  'uuuuu 'uuuuu1 'a .
    'uuuuu -> 'uuuuu1 -> (unit, unit) FStar_Tactics_Effect.tac_repr
  =
  fun uu___1 ->
    fun uu___ ->
      (fun _solution ->
         fun _binder_name ->
           Obj.magic (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> ())))
        uu___1 uu___
let rec solve_mp_for_single_hyp :
  'a .
    varname ->
      pattern ->
        hypothesis Prims.list ->
          (matching_solution -> ('a, unit) FStar_Tactics_Effect.tac_repr) ->
            matching_solution -> ('a, unit) FStar_Tactics_Effect.tac_repr
  =
  fun uu___4 ->
    fun uu___3 ->
      fun uu___2 ->
        fun uu___1 ->
          fun uu___ ->
            (fun name ->
               fun pat ->
                 fun hypotheses ->
                   fun body ->
                     fun part_sol ->
                       match hypotheses with
                       | [] ->
                           Obj.magic
                             (Obj.repr
                                (FStar_Tactics_Derived.fail
                                   "No matching hypothesis"))
                       | h::hs ->
                           Obj.magic
                             (Obj.repr
                                (FStar_Tactics_Derived.or_else
                                   (fun uu___ ->
                                      FStar_Tactics_Effect.tac_bind
                                        (FStar_Range.mk_range
                                           "FStar.Tactics.PatternMatching.fst"
                                           (Prims.of_int (448))
                                           (Prims.of_int (15))
                                           (Prims.of_int (448))
                                           (Prims.of_int (73)))
                                        (FStar_Range.mk_range
                                           "FStar.Tactics.PatternMatching.fst"
                                           (Prims.of_int (448))
                                           (Prims.of_int (9))
                                           (Prims.of_int (453))
                                           (Prims.of_int (73)))
                                        (Obj.magic
                                           (interp_pattern_aux pat
                                              part_sol.ms_vars
                                              (FStar_Reflection_Derived.type_of_binder
                                                 h)))
                                        (fun uu___1 ->
                                           (fun uu___1 ->
                                              match uu___1 with
                                              | Failure ex ->
                                                  Obj.magic
                                                    (FStar_Tactics_Effect.tac_bind
                                                       (FStar_Range.mk_range
                                                          "FStar.Tactics.PatternMatching.fst"
                                                          (Prims.of_int (450))
                                                          (Prims.of_int (16))
                                                          (Prims.of_int (450))
                                                          (Prims.of_int (74)))
                                                       (FStar_Range.mk_range
                                                          "FStar.Tactics.PatternMatching.fst"
                                                          (Prims.of_int (450))
                                                          (Prims.of_int (11))
                                                          (Prims.of_int (450))
                                                          (Prims.of_int (74)))
                                                       (Obj.magic
                                                          (FStar_Tactics_Effect.tac_bind
                                                             (FStar_Range.mk_range
                                                                "FStar.Tactics.PatternMatching.fst"
                                                                (Prims.of_int (450))
                                                                (Prims.of_int (43))
                                                                (Prims.of_int (450))
                                                                (Prims.of_int (73)))
                                                             (FStar_Range.mk_range
                                                                "prims.fst"
                                                                (Prims.of_int (590))
                                                                (Prims.of_int (19))
                                                                (Prims.of_int (590))
                                                                (Prims.of_int (31)))
                                                             (Obj.magic
                                                                (string_of_match_exception
                                                                   ex))
                                                             (fun uu___2 ->
                                                                FStar_Tactics_Effect.lift_div_tac
                                                                  (fun uu___3
                                                                    ->
                                                                    Prims.strcat
                                                                    "Failed to match hyp: "
                                                                    uu___2))))
                                                       (fun uu___2 ->
                                                          FStar_Tactics_Derived.fail
                                                            uu___2))
                                              | Success bindings1 ->
                                                  Obj.magic
                                                    (FStar_Tactics_Effect.tac_bind
                                                       (FStar_Range.mk_range
                                                          "FStar.Tactics.PatternMatching.fst"
                                                          (Prims.of_int (452))
                                                          (Prims.of_int (25))
                                                          (Prims.of_int (452))
                                                          (Prims.of_int (54)))
                                                       (FStar_Range.mk_range
                                                          "FStar.Tactics.PatternMatching.fst"
                                                          (Prims.of_int (453))
                                                          (Prims.of_int (11))
                                                          (Prims.of_int (453))
                                                          (Prims.of_int (73)))
                                                       (FStar_Tactics_Effect.lift_div_tac
                                                          (fun uu___2 ->
                                                             (name, h) ::
                                                             (part_sol.ms_hyps)))
                                                       (fun uu___2 ->
                                                          (fun ms_hyps ->
                                                             Obj.magic
                                                               (body
                                                                  {
                                                                    ms_vars =
                                                                    bindings1;
                                                                    ms_hyps
                                                                  })) uu___2)))
                                             uu___1))
                                   (fun uu___ ->
                                      solve_mp_for_single_hyp name pat hs
                                        body part_sol)))) uu___4 uu___3
              uu___2 uu___1 uu___
let rec solve_mp_for_hyps :
  'a .
    (varname * pattern) Prims.list ->
      hypothesis Prims.list ->
        (matching_solution -> ('a, unit) FStar_Tactics_Effect.tac_repr) ->
          matching_solution -> ('a, unit) FStar_Tactics_Effect.tac_repr
  =
  fun mp_hyps ->
    fun hypotheses ->
      fun body ->
        fun partial_solution ->
          match mp_hyps with
          | [] -> body partial_solution
          | (name, pat)::pats ->
              solve_mp_for_single_hyp name pat hypotheses
                (solve_mp_for_hyps pats hypotheses body) partial_solution
let solve_mp :
  'a .
    matching_problem ->
      FStar_Reflection_Types.binders ->
        FStar_Reflection_Types.term ->
          (matching_solution -> ('a, unit) FStar_Tactics_Effect.tac_repr) ->
            ('a, unit) FStar_Tactics_Effect.tac_repr
  =
  fun problem ->
    fun hypotheses ->
      fun goal ->
        fun body ->
          FStar_Tactics_Effect.tac_bind
            (FStar_Range.mk_range "FStar.Tactics.PatternMatching.fst"
               (Prims.of_int (481)) (Prims.of_int (4)) (Prims.of_int (486))
               (Prims.of_int (64)))
            (FStar_Range.mk_range "FStar.Tactics.PatternMatching.fst"
               (Prims.of_int (487)) (Prims.of_int (2)) (Prims.of_int (487))
               (Prims.of_int (62)))
            (match problem.mp_goal with
             | FStar_Pervasives_Native.None ->
                 Obj.magic
                   (Obj.repr
                      (FStar_Tactics_Effect.lift_div_tac
                         (fun uu___ -> { ms_vars = []; ms_hyps = [] })))
             | FStar_Pervasives_Native.Some pat ->
                 Obj.magic
                   (Obj.repr
                      (FStar_Tactics_Effect.tac_bind
                         (FStar_Range.mk_range
                            "FStar.Tactics.PatternMatching.fst"
                            (Prims.of_int (484)) (Prims.of_int (12))
                            (Prims.of_int (484)) (Prims.of_int (35)))
                         (FStar_Range.mk_range
                            "FStar.Tactics.PatternMatching.fst"
                            (Prims.of_int (484)) (Prims.of_int (6))
                            (Prims.of_int (486)) (Prims.of_int (64)))
                         (Obj.magic (interp_pattern pat goal))
                         (fun uu___ ->
                            (fun uu___ ->
                               match uu___ with
                               | Failure ex ->
                                   Obj.magic
                                     (Obj.repr
                                        (FStar_Tactics_Effect.tac_bind
                                           (FStar_Range.mk_range
                                              "FStar.Tactics.PatternMatching.fst"
                                              (Prims.of_int (485))
                                              (Prims.of_int (27))
                                              (Prims.of_int (485))
                                              (Prims.of_int (86)))
                                           (FStar_Range.mk_range
                                              "FStar.Tactics.PatternMatching.fst"
                                              (Prims.of_int (485))
                                              (Prims.of_int (22))
                                              (Prims.of_int (485))
                                              (Prims.of_int (86)))
                                           (Obj.magic
                                              (FStar_Tactics_Effect.tac_bind
                                                 (FStar_Range.mk_range
                                                    "FStar.Tactics.PatternMatching.fst"
                                                    (Prims.of_int (485))
                                                    (Prims.of_int (55))
                                                    (Prims.of_int (485))
                                                    (Prims.of_int (85)))
                                                 (FStar_Range.mk_range
                                                    "prims.fst"
                                                    (Prims.of_int (590))
                                                    (Prims.of_int (19))
                                                    (Prims.of_int (590))
                                                    (Prims.of_int (31)))
                                                 (Obj.magic
                                                    (string_of_match_exception
                                                       ex))
                                                 (fun uu___1 ->
                                                    FStar_Tactics_Effect.lift_div_tac
                                                      (fun uu___2 ->
                                                         Prims.strcat
                                                           "Failed to match goal: "
                                                           uu___1))))
                                           (fun uu___1 ->
                                              FStar_Tactics_Derived.fail
                                                uu___1)))
                               | Success bindings1 ->
                                   Obj.magic
                                     (Obj.repr
                                        (FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___1 ->
                                              {
                                                ms_vars = bindings1;
                                                ms_hyps = []
                                              })))) uu___))))
            (fun uu___ ->
               (fun goal_ps ->
                  Obj.magic
                    (solve_mp_for_hyps problem.mp_hyps hypotheses body
                       goal_ps)) uu___)
let rec (pattern_of_term_ex :
  FStar_Reflection_Types.term ->
    (pattern match_res, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun tm ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Range.mk_range "FStar.Tactics.PatternMatching.fst"
         (Prims.of_int (507)) (Prims.of_int (8)) (Prims.of_int (507))
         (Prims.of_int (18)))
      (FStar_Range.mk_range "FStar.Tactics.PatternMatching.fst"
         (Prims.of_int (507)) (Prims.of_int (2)) (Prims.of_int (520))
         (Prims.of_int (44))) (Obj.magic (FStar_Tactics_Builtins.inspect tm))
      (fun uu___ ->
         (fun uu___ ->
            match uu___ with
            | FStar_Reflection_Data.Tv_Var bv ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.tac_bind
                        (FStar_Range.mk_range
                           "FStar.Tactics.PatternMatching.fst"
                           (Prims.of_int (509)) (Prims.of_int (11))
                           (Prims.of_int (509)) (Prims.of_int (33)))
                        (FStar_Range.mk_range
                           "FStar.Tactics.PatternMatching.fst"
                           (Prims.of_int (509)) (Prims.of_int (4))
                           (Prims.of_int (509)) (Prims.of_int (33)))
                        (Obj.magic
                           (FStar_Tactics_Effect.tac_bind
                              (FStar_Range.mk_range
                                 "FStar.Tactics.PatternMatching.fst"
                                 (Prims.of_int (509)) (Prims.of_int (17))
                                 (Prims.of_int (509)) (Prims.of_int (32)))
                              (FStar_Range.mk_range
                                 "FStar.Tactics.PatternMatching.fst"
                                 (Prims.of_int (509)) (Prims.of_int (11))
                                 (Prims.of_int (509)) (Prims.of_int (33)))
                              (Obj.magic
                                 (FStar_Tactics_Derived.name_of_bv bv))
                              (fun uu___1 ->
                                 FStar_Tactics_Effect.lift_div_tac
                                   (fun uu___2 -> PVar uu___1))))
                        (fun uu___1 ->
                           FStar_Tactics_Effect.lift_div_tac
                             (fun uu___2 -> return uu___1))))
            | FStar_Reflection_Data.Tv_FVar fv ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.lift_div_tac
                        (fun uu___1 ->
                           return
                             (PQn (FStar_Reflection_Derived.fv_to_string fv)))))
            | FStar_Reflection_Data.Tv_UInst (fv, uu___1) ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.lift_div_tac
                        (fun uu___2 ->
                           return
                             (PQn (FStar_Reflection_Derived.fv_to_string fv)))))
            | FStar_Reflection_Data.Tv_Type uu___1 ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.lift_div_tac
                        (fun uu___2 -> return PType)))
            | FStar_Reflection_Data.Tv_App (f, (x, uu___1)) ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.tac_bind
                        (FStar_Range.mk_range
                           "FStar.Tactics.PatternMatching.fst"
                           (Prims.of_int (517)) (Prims.of_int (17))
                           (Prims.of_int (517)) (Prims.of_int (37)))
                        (FStar_Range.mk_range
                           "FStar.Tactics.PatternMatching.fst"
                           (Prims.of_int (517)) (Prims.of_int (5))
                           (Prims.of_int (519)) (Prims.of_int (28)))
                        (Obj.magic (pattern_of_term_ex f))
                        (fun uu___2 ->
                           (fun uu___2 ->
                              Obj.magic
                                (op_let_Question uu___2
                                   (fun fpat ->
                                      FStar_Tactics_Effect.tac_bind
                                        (FStar_Range.mk_range
                                           "FStar.Tactics.PatternMatching.fst"
                                           (Prims.of_int (518))
                                           (Prims.of_int (17))
                                           (Prims.of_int (518))
                                           (Prims.of_int (37)))
                                        (FStar_Range.mk_range
                                           "FStar.Tactics.PatternMatching.fst"
                                           (Prims.of_int (518))
                                           (Prims.of_int (5))
                                           (Prims.of_int (519))
                                           (Prims.of_int (28)))
                                        (Obj.magic (pattern_of_term_ex x))
                                        (fun uu___3 ->
                                           (fun uu___3 ->
                                              Obj.magic
                                                (op_let_Question uu___3
                                                   (fun uu___4 ->
                                                      (fun xpat ->
                                                         Obj.magic
                                                           (FStar_Tactics_Effect.lift_div_tac
                                                              (fun uu___4 ->
                                                                 return
                                                                   (PApp
                                                                    (fpat,
                                                                    xpat)))))
                                                        uu___4))) uu___3))))
                             uu___2)))
            | uu___1 ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.lift_div_tac
                        (fun uu___2 -> raise (UnsupportedTermInPattern tm)))))
           uu___)
let (beta_reduce :
  FStar_Reflection_Types.term ->
    (FStar_Reflection_Types.term, unit) FStar_Tactics_Effect.tac_repr)
  = fun tm -> FStar_Tactics_Derived.norm_term [] tm
let (pattern_of_term :
  FStar_Reflection_Types.term ->
    (pattern, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun tm ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Range.mk_range "FStar.Tactics.PatternMatching.fst"
         (Prims.of_int (530)) (Prims.of_int (10)) (Prims.of_int (530))
         (Prims.of_int (31)))
      (FStar_Range.mk_range "FStar.Tactics.PatternMatching.fst"
         (Prims.of_int (530)) (Prims.of_int (4)) (Prims.of_int (532))
         (Prims.of_int (63))) (Obj.magic (pattern_of_term_ex tm))
      (fun uu___ ->
         (fun uu___ ->
            match uu___ with
            | Success bb ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> bb)))
            | Failure ex ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.tac_bind
                        (FStar_Range.mk_range
                           "FStar.Tactics.PatternMatching.fst"
                           (Prims.of_int (532)) (Prims.of_int (33))
                           (Prims.of_int (532)) (Prims.of_int (63)))
                        (FStar_Range.mk_range
                           "FStar.Tactics.PatternMatching.fst"
                           (Prims.of_int (532)) (Prims.of_int (20))
                           (Prims.of_int (532)) (Prims.of_int (63)))
                        (Obj.magic (string_of_match_exception ex))
                        (fun uu___1 -> FStar_Tactics_Derived.fail uu___1))))
           uu___)
type 'a hyp = FStar_Reflection_Types.binder
type 'a pm_goal = unit
let (hyp_qn : Prims.string) = "FStar.Tactics.PatternMatching.hyp"
let (goal_qn : Prims.string) = "FStar.Tactics.PatternMatching.pm_goal"
type abspat_binder_kind =
  | ABKVar of FStar_Reflection_Types.typ 
  | ABKHyp 
  | ABKGoal 
let (uu___is_ABKVar : abspat_binder_kind -> Prims.bool) =
  fun projectee -> match projectee with | ABKVar _0 -> true | uu___ -> false
let (__proj__ABKVar__item___0 :
  abspat_binder_kind -> FStar_Reflection_Types.typ) =
  fun projectee -> match projectee with | ABKVar _0 -> _0
let (uu___is_ABKHyp : abspat_binder_kind -> Prims.bool) =
  fun projectee -> match projectee with | ABKHyp -> true | uu___ -> false
let (uu___is_ABKGoal : abspat_binder_kind -> Prims.bool) =
  fun projectee -> match projectee with | ABKGoal -> true | uu___ -> false
let (string_of_abspat_binder_kind : abspat_binder_kind -> Prims.string) =
  fun uu___ ->
    match uu___ with
    | ABKVar uu___1 -> "varname"
    | ABKHyp -> "hyp"
    | ABKGoal -> "goal"
type abspat_argspec = {
  asa_name: absvar ;
  asa_kind: abspat_binder_kind }
let (__proj__Mkabspat_argspec__item__asa_name : abspat_argspec -> absvar) =
  fun projectee -> match projectee with | { asa_name; asa_kind;_} -> asa_name
let (__proj__Mkabspat_argspec__item__asa_kind :
  abspat_argspec -> abspat_binder_kind) =
  fun projectee -> match projectee with | { asa_name; asa_kind;_} -> asa_kind
type abspat_continuation =
  (abspat_argspec Prims.list * FStar_Reflection_Types.term)
let (classify_abspat_binder :
  FStar_Reflection_Types.binder ->
    ((abspat_binder_kind * FStar_Reflection_Types.term), unit)
      FStar_Tactics_Effect.tac_repr)
  =
  fun binder ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Range.mk_range "FStar.Tactics.PatternMatching.fst"
         (Prims.of_int (584)) (Prims.of_int (16)) (Prims.of_int (584))
         (Prims.of_int (19)))
      (FStar_Range.mk_range "FStar.Tactics.PatternMatching.fst"
         (Prims.of_int (584)) (Prims.of_int (22)) (Prims.of_int (585))
         (Prims.of_int (51)))
      (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> "v"))
      (fun uu___ ->
         (fun varname1 ->
            Obj.magic
              (FStar_Tactics_Effect.tac_bind
                 (FStar_Range.mk_range "FStar.Tactics.PatternMatching.fst"
                    (Prims.of_int (585)) (Prims.of_int (16))
                    (Prims.of_int (585)) (Prims.of_int (48)))
                 (FStar_Range.mk_range "FStar.Tactics.PatternMatching.fst"
                    (Prims.of_int (585)) (Prims.of_int (51))
                    (Prims.of_int (586)) (Prims.of_int (53)))
                 (FStar_Tactics_Effect.lift_div_tac
                    (fun uu___ -> PApp ((PQn hyp_qn), (PVar varname1))))
                 (fun uu___ ->
                    (fun hyp_pat ->
                       Obj.magic
                         (FStar_Tactics_Effect.tac_bind
                            (FStar_Range.mk_range
                               "FStar.Tactics.PatternMatching.fst"
                               (Prims.of_int (586)) (Prims.of_int (17))
                               (Prims.of_int (586)) (Prims.of_int (50)))
                            (FStar_Range.mk_range
                               "FStar.Tactics.PatternMatching.fst"
                               (Prims.of_int (586)) (Prims.of_int (53))
                               (Prims.of_int (588)) (Prims.of_int (36)))
                            (FStar_Tactics_Effect.lift_div_tac
                               (fun uu___ ->
                                  PApp ((PQn goal_qn), (PVar varname1))))
                            (fun uu___ ->
                               (fun goal_pat ->
                                  Obj.magic
                                    (FStar_Tactics_Effect.tac_bind
                                       (FStar_Range.mk_range
                                          "FStar.Tactics.PatternMatching.fst"
                                          (Prims.of_int (588))
                                          (Prims.of_int (12))
                                          (Prims.of_int (588))
                                          (Prims.of_int (33)))
                                       (FStar_Range.mk_range
                                          "FStar.Tactics.PatternMatching.fst"
                                          (Prims.of_int (589))
                                          (Prims.of_int (2))
                                          (Prims.of_int (596))
                                          (Prims.of_int (34)))
                                       (FStar_Tactics_Effect.lift_div_tac
                                          (fun uu___ ->
                                             FStar_Reflection_Derived.type_of_binder
                                               binder))
                                       (fun uu___ ->
                                          (fun typ ->
                                             Obj.magic
                                               (FStar_Tactics_Effect.tac_bind
                                                  (FStar_Range.mk_range
                                                     "FStar.Tactics.PatternMatching.fst"
                                                     (Prims.of_int (589))
                                                     (Prims.of_int (8))
                                                     (Prims.of_int (589))
                                                     (Prims.of_int (34)))
                                                  (FStar_Range.mk_range
                                                     "FStar.Tactics.PatternMatching.fst"
                                                     (Prims.of_int (589))
                                                     (Prims.of_int (2))
                                                     (Prims.of_int (596))
                                                     (Prims.of_int (34)))
                                                  (Obj.magic
                                                     (interp_pattern hyp_pat
                                                        typ))
                                                  (fun uu___ ->
                                                     (fun uu___ ->
                                                        match uu___ with
                                                        | Success
                                                            ((uu___1,
                                                              hyp_typ)::[])
                                                            ->
                                                            Obj.magic
                                                              (Obj.repr
                                                                 (FStar_Tactics_Effect.lift_div_tac
                                                                    (
                                                                    fun
                                                                    uu___2 ->
                                                                    (ABKHyp,
                                                                    hyp_typ))))
                                                        | Success uu___1 ->
                                                            Obj.magic
                                                              (Obj.repr
                                                                 (FStar_Tactics_Derived.fail
                                                                    "classifiy_abspat_binder: impossible (1)"))
                                                        | Failure uu___1 ->
                                                            Obj.magic
                                                              (Obj.repr
                                                                 (FStar_Tactics_Effect.tac_bind
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (593))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (593))
                                                                    (Prims.of_int (37)))
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (593))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (596))
                                                                    (Prims.of_int (34)))
                                                                    (
                                                                    Obj.magic
                                                                    (interp_pattern
                                                                    goal_pat
                                                                    typ))
                                                                    (
                                                                    fun
                                                                    uu___2 ->
                                                                    match uu___2
                                                                    with
                                                                    | 
                                                                    Success
                                                                    ((uu___3,
                                                                    goal_typ)::[])
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    (ABKGoal,
                                                                    goal_typ))
                                                                    | 
                                                                    Success
                                                                    uu___3 ->
                                                                    FStar_Tactics_Derived.fail
                                                                    "classifiy_abspat_binder: impossible (2)"
                                                                    | 
                                                                    Failure
                                                                    uu___3 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    ((ABKVar
                                                                    typ),
                                                                    typ))))))
                                                       uu___))) uu___)))
                                 uu___))) uu___))) uu___)
let rec (binders_and_body_of_abs :
  FStar_Reflection_Types.term ->
    ((FStar_Reflection_Types.binders * FStar_Reflection_Types.term), 
      unit) FStar_Tactics_Effect.tac_repr)
  =
  fun tm ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Range.mk_range "FStar.Tactics.PatternMatching.fst"
         (Prims.of_int (600)) (Prims.of_int (8)) (Prims.of_int (600))
         (Prims.of_int (18)))
      (FStar_Range.mk_range "FStar.Tactics.PatternMatching.fst"
         (Prims.of_int (600)) (Prims.of_int (2)) (Prims.of_int (604))
         (Prims.of_int (15))) (Obj.magic (FStar_Tactics_Builtins.inspect tm))
      (fun uu___ ->
         (fun uu___ ->
            match uu___ with
            | FStar_Reflection_Data.Tv_Abs (binder, tm1) ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.tac_bind
                        (FStar_Range.mk_range
                           "FStar.Tactics.PatternMatching.fst"
                           (Prims.of_int (602)) (Prims.of_int (24))
                           (Prims.of_int (602)) (Prims.of_int (50)))
                        (FStar_Range.mk_range
                           "FStar.Tactics.PatternMatching.fst"
                           (Prims.of_int (601)) (Prims.of_int (23))
                           (Prims.of_int (602)) (Prims.of_int (53)))
                        (Obj.magic (binders_and_body_of_abs tm1))
                        (fun uu___1 ->
                           FStar_Tactics_Effect.lift_div_tac
                             (fun uu___2 ->
                                match uu___1 with
                                | (binders, body) ->
                                    ((binder :: binders), body)))))
            | uu___1 ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.lift_div_tac
                        (fun uu___2 -> ([], tm))))) uu___)
let (cleanup_abspat :
  FStar_Reflection_Types.term ->
    (FStar_Reflection_Types.term, unit) FStar_Tactics_Effect.tac_repr)
  = fun t -> FStar_Tactics_Derived.norm_term [] t
let (matching_problem_of_abs :
  FStar_Reflection_Types.term ->
    ((matching_problem * abspat_continuation), unit)
      FStar_Tactics_Effect.tac_repr)
  =
  fun tm ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Range.mk_range "FStar.Tactics.PatternMatching.fst"
         (Prims.of_int (626)) (Prims.of_int (22)) (Prims.of_int (626))
         (Prims.of_int (65)))
      (FStar_Range.mk_range "FStar.Tactics.PatternMatching.fst"
         (Prims.of_int (624)) (Prims.of_int (52)) (Prims.of_int (626))
         (Prims.of_int (68)))
      (Obj.magic
         (FStar_Tactics_Effect.tac_bind
            (FStar_Range.mk_range "FStar.Tactics.PatternMatching.fst"
               (Prims.of_int (626)) (Prims.of_int (46)) (Prims.of_int (626))
               (Prims.of_int (65)))
            (FStar_Range.mk_range "FStar.Tactics.PatternMatching.fst"
               (Prims.of_int (626)) (Prims.of_int (22)) (Prims.of_int (626))
               (Prims.of_int (65))) (Obj.magic (cleanup_abspat tm))
            (fun uu___ ->
               (fun uu___ -> Obj.magic (binders_and_body_of_abs uu___)) uu___)))
      (fun uu___ ->
         (fun uu___ ->
            match uu___ with
            | (binders, body) ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Range.mk_range
                        "FStar.Tactics.PatternMatching.fst"
                        (Prims.of_int (627)) (Prims.of_int (2))
                        (Prims.of_int (628)) (Prims.of_int (66)))
                     (FStar_Range.mk_range
                        "FStar.Tactics.PatternMatching.fst"
                        (Prims.of_int (628)) (Prims.of_int (67))
                        (Prims.of_int (637)) (Prims.of_int (16)))
                     (Obj.magic
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Range.mk_range
                              "FStar.Tactics.PatternMatching.fst"
                              (Prims.of_int (627)) (Prims.of_int (8))
                              (Prims.of_int (628)) (Prims.of_int (66)))
                           (FStar_Range.mk_range
                              "FStar.Tactics.PatternMatching.fst"
                              (Prims.of_int (627)) (Prims.of_int (2))
                              (Prims.of_int (628)) (Prims.of_int (66)))
                           (Obj.magic
                              (FStar_Tactics_Effect.tac_bind
                                 (FStar_Range.mk_range
                                    "FStar.Tactics.PatternMatching.fst"
                                    (Prims.of_int (627)) (Prims.of_int (27))
                                    (Prims.of_int (628)) (Prims.of_int (65)))
                                 (FStar_Range.mk_range "prims.fst"
                                    (Prims.of_int (590)) (Prims.of_int (19))
                                    (Prims.of_int (590)) (Prims.of_int (31)))
                                 (Obj.magic
                                    (FStar_Tactics_Effect.tac_bind
                                       (FStar_Range.mk_range
                                          "FStar.Tactics.PatternMatching.fst"
                                          (Prims.of_int (628))
                                          (Prims.of_int (9))
                                          (Prims.of_int (628))
                                          (Prims.of_int (64)))
                                       (FStar_Range.mk_range
                                          "FStar.Tactics.PatternMatching.fst"
                                          (Prims.of_int (627))
                                          (Prims.of_int (27))
                                          (Prims.of_int (628))
                                          (Prims.of_int (65)))
                                       (Obj.magic
                                          (FStar_Tactics_Util.map
                                             (fun b ->
                                                FStar_Tactics_Derived.name_of_binder
                                                  b) binders))
                                       (fun uu___1 ->
                                          FStar_Tactics_Effect.lift_div_tac
                                            (fun uu___2 ->
                                               FStar_String.concat ", "
                                                 uu___1))))
                                 (fun uu___1 ->
                                    FStar_Tactics_Effect.lift_div_tac
                                      (fun uu___2 ->
                                         Prims.strcat "Got binders: " uu___1))))
                           (fun uu___1 ->
                              (fun uu___1 -> Obj.magic (debug uu___1)) uu___1)))
                     (fun uu___1 ->
                        (fun uu___1 ->
                           Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Range.mk_range
                                   "FStar.Tactics.PatternMatching.fst"
                                   (Prims.of_int (631)) (Prims.of_int (4))
                                   (Prims.of_int (637)) (Prims.of_int (13)))
                                (FStar_Range.mk_range
                                   "FStar.Tactics.PatternMatching.fst"
                                   (Prims.of_int (637)) (Prims.of_int (16))
                                   (Prims.of_int (651)) (Prims.of_int (27)))
                                (Obj.magic
                                   (FStar_Tactics_Util.map
                                      (fun binder ->
                                         FStar_Tactics_Effect.tac_bind
                                           (FStar_Range.mk_range
                                              "FStar.Tactics.PatternMatching.fst"
                                              (Prims.of_int (632))
                                              (Prims.of_int (22))
                                              (Prims.of_int (632))
                                              (Prims.of_int (43)))
                                           (FStar_Range.mk_range
                                              "FStar.Tactics.PatternMatching.fst"
                                              (Prims.of_int (633))
                                              (Prims.of_int (8))
                                              (Prims.of_int (636))
                                              (Prims.of_int (43)))
                                           (Obj.magic
                                              (FStar_Tactics_Derived.name_of_binder
                                                 binder))
                                           (fun uu___2 ->
                                              (fun bv_name ->
                                                 Obj.magic
                                                   (FStar_Tactics_Effect.tac_bind
                                                      (FStar_Range.mk_range
                                                         "FStar.Tactics.PatternMatching.fst"
                                                         (Prims.of_int (633))
                                                         (Prims.of_int (8))
                                                         (Prims.of_int (634))
                                                         (Prims.of_int (54)))
                                                      (FStar_Range.mk_range
                                                         "FStar.Tactics.PatternMatching.fst"
                                                         (Prims.of_int (634))
                                                         (Prims.of_int (55))
                                                         (Prims.of_int (635))
                                                         (Prims.of_int (63)))
                                                      (Obj.magic
                                                         (FStar_Tactics_Effect.tac_bind
                                                            (FStar_Range.mk_range
                                                               "FStar.Tactics.PatternMatching.fst"
                                                               (Prims.of_int (633))
                                                               (Prims.of_int (14))
                                                               (Prims.of_int (634))
                                                               (Prims.of_int (54)))
                                                            (FStar_Range.mk_range
                                                               "FStar.Tactics.PatternMatching.fst"
                                                               (Prims.of_int (633))
                                                               (Prims.of_int (8))
                                                               (Prims.of_int (634))
                                                               (Prims.of_int (54)))
                                                            (Obj.magic
                                                               (FStar_Tactics_Effect.tac_bind
                                                                  (FStar_Range.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (633))
                                                                    (Prims.of_int (32))
                                                                    (Prims.of_int (634))
                                                                    (Prims.of_int (53)))
                                                                  (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (31)))
                                                                  (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (633))
                                                                    (Prims.of_int (42))
                                                                    (Prims.of_int (634))
                                                                    (Prims.of_int (53)))
                                                                    (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (31)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (634))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (634))
                                                                    (Prims.of_int (53)))
                                                                    (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (31)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Builtins.term_to_string
                                                                    (FStar_Reflection_Derived.type_of_binder
                                                                    binder)))
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    Prims.strcat
                                                                    "; type is "
                                                                    uu___2))))
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    Prims.strcat
                                                                    bv_name
                                                                    uu___2))))
                                                                  (fun uu___2
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    Prims.strcat
                                                                    "Got binder: "
                                                                    uu___2))))
                                                            (fun uu___2 ->
                                                               (fun uu___2 ->
                                                                  Obj.magic
                                                                    (
                                                                    debug
                                                                    uu___2))
                                                                 uu___2)))
                                                      (fun uu___2 ->
                                                         (fun uu___2 ->
                                                            Obj.magic
                                                              (FStar_Tactics_Effect.tac_bind
                                                                 (FStar_Range.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (635))
                                                                    (Prims.of_int (31))
                                                                    (Prims.of_int (635))
                                                                    (Prims.of_int (60)))
                                                                 (FStar_Range.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (634))
                                                                    (Prims.of_int (55))
                                                                    (Prims.of_int (635))
                                                                    (Prims.of_int (63)))
                                                                 (Obj.magic
                                                                    (
                                                                    classify_abspat_binder
                                                                    binder))
                                                                 (fun uu___3
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    match uu___3
                                                                    with
                                                                    | 
                                                                    (binder_kind,
                                                                    typ) ->
                                                                    (binder,
                                                                    bv_name,
                                                                    binder_kind,
                                                                    typ)))))
                                                           uu___2))) uu___2))
                                      binders))
                                (fun uu___2 ->
                                   (fun classified_binders ->
                                      Obj.magic
                                        (FStar_Tactics_Effect.tac_bind
                                           (FStar_Range.mk_range
                                              "FStar.Tactics.PatternMatching.fst"
                                              (Prims.of_int (640))
                                              (Prims.of_int (4))
                                              (Prims.of_int (651))
                                              (Prims.of_int (24)))
                                           (FStar_Range.mk_range
                                              "FStar.Tactics.PatternMatching.fst"
                                              (Prims.of_int (651))
                                              (Prims.of_int (27))
                                              (Prims.of_int (657))
                                              (Prims.of_int (60)))
                                           (Obj.magic
                                              (FStar_Tactics_Util.fold_left
                                                 (fun problem ->
                                                    fun uu___2 ->
                                                      match uu___2 with
                                                      | (binder, bv_name,
                                                         binder_kind, typ) ->
                                                          FStar_Tactics_Effect.tac_bind
                                                            (FStar_Range.mk_range
                                                               "FStar.Tactics.PatternMatching.fst"
                                                               (Prims.of_int (642))
                                                               (Prims.of_int (9))
                                                               (Prims.of_int (644))
                                                               (Prims.of_int (52)))
                                                            (FStar_Range.mk_range
                                                               "FStar.Tactics.PatternMatching.fst"
                                                               (Prims.of_int (645))
                                                               (Prims.of_int (9))
                                                               (Prims.of_int (649))
                                                               (Prims.of_int (75)))
                                                            (Obj.magic
                                                               (FStar_Tactics_Effect.tac_bind
                                                                  (FStar_Range.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (642))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (644))
                                                                    (Prims.of_int (52)))
                                                                  (FStar_Range.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (642))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (644))
                                                                    (Prims.of_int (52)))
                                                                  (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (642))
                                                                    (Prims.of_int (38))
                                                                    (Prims.of_int (644))
                                                                    (Prims.of_int (51)))
                                                                    (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (31)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (642))
                                                                    (Prims.of_int (38))
                                                                    (Prims.of_int (642))
                                                                    (Prims.of_int (59)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (642))
                                                                    (Prims.of_int (38))
                                                                    (Prims.of_int (644))
                                                                    (Prims.of_int (51)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Derived.name_of_binder
                                                                    binder))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (643))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (644))
                                                                    (Prims.of_int (51)))
                                                                    (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (31)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (643))
                                                                    (Prims.of_int (37))
                                                                    (Prims.of_int (644))
                                                                    (Prims.of_int (51)))
                                                                    (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (31)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (644))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (644))
                                                                    (Prims.of_int (51)))
                                                                    (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (31)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (644))
                                                                    (Prims.of_int (33))
                                                                    (Prims.of_int (644))
                                                                    (Prims.of_int (51)))
                                                                    (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (31)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Builtins.term_to_string
                                                                    typ))
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    Prims.strcat
                                                                    ", with type "
                                                                    uu___4))))
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    Prims.strcat
                                                                    (string_of_abspat_binder_kind
                                                                    binder_kind)
                                                                    uu___4))))
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    Prims.strcat
                                                                    ", classified as "
                                                                    uu___4))))
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    Prims.strcat
                                                                    uu___3
                                                                    uu___4))))
                                                                    uu___3)))
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    Prims.strcat
                                                                    "Compiling binder "
                                                                    uu___3))))
                                                                  (fun uu___3
                                                                    ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    Obj.magic
                                                                    (debug
                                                                    uu___3))
                                                                    uu___3)))
                                                            (fun uu___3 ->
                                                               (fun uu___3 ->
                                                                  match binder_kind
                                                                  with
                                                                  | ABKVar
                                                                    uu___4 ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    {
                                                                    mp_vars =
                                                                    (bv_name
                                                                    ::
                                                                    (problem.mp_vars));
                                                                    mp_hyps =
                                                                    (problem.mp_hyps);
                                                                    mp_goal =
                                                                    (problem.mp_goal)
                                                                    })))
                                                                  | ABKHyp ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (647))
                                                                    (Prims.of_int (46))
                                                                    (Prims.of_int (648))
                                                                    (Prims.of_int (63)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (647))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (648))
                                                                    (Prims.of_int (63)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (647))
                                                                    (Prims.of_int (46))
                                                                    (Prims.of_int (647))
                                                                    (Prims.of_int (78)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (647))
                                                                    (Prims.of_int (46))
                                                                    (Prims.of_int (648))
                                                                    (Prims.of_int (63)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (647))
                                                                    (Prims.of_int (56))
                                                                    (Prims.of_int (647))
                                                                    (Prims.of_int (77)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (647))
                                                                    (Prims.of_int (46))
                                                                    (Prims.of_int (647))
                                                                    (Prims.of_int (78)))
                                                                    (Obj.magic
                                                                    (pattern_of_term
                                                                    typ))
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    (bv_name,
                                                                    uu___4)))))
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    uu___4 ::
                                                                    (problem.mp_hyps)))))
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    {
                                                                    mp_vars =
                                                                    (problem.mp_vars);
                                                                    mp_hyps =
                                                                    uu___4;
                                                                    mp_goal =
                                                                    (problem.mp_goal)
                                                                    }))))
                                                                  | ABKGoal
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (649))
                                                                    (Prims.of_int (47))
                                                                    (Prims.of_int (649))
                                                                    (Prims.of_int (73)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (649))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (649))
                                                                    (Prims.of_int (73)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (649))
                                                                    (Prims.of_int (52))
                                                                    (Prims.of_int (649))
                                                                    (Prims.of_int (73)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (649))
                                                                    (Prims.of_int (47))
                                                                    (Prims.of_int (649))
                                                                    (Prims.of_int (73)))
                                                                    (Obj.magic
                                                                    (pattern_of_term
                                                                    typ))
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Pervasives_Native.Some
                                                                    uu___4))))
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    {
                                                                    mp_vars =
                                                                    (problem.mp_vars);
                                                                    mp_hyps =
                                                                    (problem.mp_hyps);
                                                                    mp_goal =
                                                                    uu___4
                                                                    })))))
                                                                 uu___3))
                                                 {
                                                   mp_vars = [];
                                                   mp_hyps = [];
                                                   mp_goal =
                                                     FStar_Pervasives_Native.None
                                                 } classified_binders))
                                           (fun uu___2 ->
                                              (fun problem ->
                                                 Obj.magic
                                                   (FStar_Tactics_Effect.tac_bind
                                                      (FStar_Range.mk_range
                                                         "FStar.Tactics.PatternMatching.fst"
                                                         (Prims.of_int (653))
                                                         (Prims.of_int (20))
                                                         (Prims.of_int (656))
                                                         (Prims.of_int (54)))
                                                      (FStar_Range.mk_range
                                                         "FStar.Tactics.PatternMatching.fst"
                                                         (Prims.of_int (657))
                                                         (Prims.of_int (60))
                                                         (Prims.of_int (662))
                                                         (Prims.of_int (36)))
                                                      (Obj.magic
                                                         (FStar_Tactics_Effect.tac_bind
                                                            (FStar_Range.mk_range
                                                               "FStar.Tactics.PatternMatching.fst"
                                                               (Prims.of_int (655))
                                                               (Prims.of_int (4))
                                                               (Prims.of_int (656))
                                                               (Prims.of_int (51)))
                                                            (FStar_Range.mk_range
                                                               "FStar.Tactics.PatternMatching.fst"
                                                               (Prims.of_int (657))
                                                               (Prims.of_int (4))
                                                               (Prims.of_int (657))
                                                               (Prims.of_int (57)))
                                                            (FStar_Tactics_Effect.lift_div_tac
                                                               (fun uu___3 ->
                                                                  fun uu___2
                                                                    ->
                                                                    (fun
                                                                    uu___2 ->
                                                                    fun xx ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    match xx
                                                                    with
                                                                    | 
                                                                    (binder,
                                                                    xx1,
                                                                    binder_kind,
                                                                    yy) ->
                                                                    {
                                                                    asa_name
                                                                    = binder;
                                                                    asa_kind
                                                                    =
                                                                    binder_kind
                                                                    })))
                                                                    uu___3
                                                                    uu___2))
                                                            (fun uu___2 ->
                                                               (fun
                                                                  abspat_argspec_of_binder
                                                                  ->
                                                                  Obj.magic
                                                                    (
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (657))
                                                                    (Prims.of_int (5))
                                                                    (Prims.of_int (657))
                                                                    (Prims.of_int (52)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (657))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (657))
                                                                    (Prims.of_int (57)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Util.map
                                                                    abspat_argspec_of_binder
                                                                    classified_binders))
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    (uu___2,
                                                                    tm)))))
                                                                 uu___2)))
                                                      (fun uu___2 ->
                                                         (fun continuation ->
                                                            Obj.magic
                                                              (FStar_Tactics_Effect.tac_bind
                                                                 (FStar_Range.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (660))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (662))
                                                                    (Prims.of_int (31)))
                                                                 (FStar_Range.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (664))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (665))
                                                                    (Prims.of_int (18)))
                                                                 (FStar_Tactics_Effect.lift_div_tac
                                                                    (
                                                                    fun
                                                                    uu___2 ->
                                                                    {
                                                                    mp_vars =
                                                                    (FStar_List_Tot_Base.rev
                                                                    problem.mp_vars);
                                                                    mp_hyps =
                                                                    (FStar_List_Tot_Base.rev
                                                                    problem.mp_hyps);
                                                                    mp_goal =
                                                                    (problem.mp_goal)
                                                                    }))
                                                                 (fun uu___2
                                                                    ->
                                                                    (fun mp
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (664))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (664))
                                                                    (Prims.of_int (68)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (665))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (665))
                                                                    (Prims.of_int (18)))
                                                                    (Obj.magic
                                                                    (debug
                                                                    (Prims.strcat
                                                                    "Got matching problem: "
                                                                    (string_of_matching_problem
                                                                    mp))))
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    (mp,
                                                                    continuation)))))
                                                                    uu___2)))
                                                           uu___2))) uu___2)))
                                     uu___2))) uu___1))) uu___)
let (arg_type_of_binder_kind :
  abspat_binder_kind ->
    (FStar_Reflection_Types.term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___ ->
    (fun binder_kind ->
       Obj.magic
         (FStar_Tactics_Effect.lift_div_tac
            (fun uu___ ->
               match binder_kind with
               | ABKVar typ -> typ
               | ABKHyp ->
                   FStar_Reflection_Builtins.pack_ln
                     (FStar_Reflection_Data.Tv_FVar
                        (FStar_Reflection_Builtins.pack_fv
                           ["FStar"; "Reflection"; "Types"; "binder"]))
               | ABKGoal ->
                   FStar_Reflection_Builtins.pack_ln
                     (FStar_Reflection_Data.Tv_FVar
                        (FStar_Reflection_Builtins.pack_fv ["Prims"; "unit"])))))
      uu___
let (locate_fn_of_binder_kind :
  abspat_binder_kind -> FStar_Reflection_Types.term) =
  fun binder_kind ->
    match binder_kind with
    | ABKVar uu___ ->
        FStar_Reflection_Builtins.pack_ln
          (FStar_Reflection_Data.Tv_FVar
             (FStar_Reflection_Builtins.pack_fv
                ["FStar"; "Tactics"; "PatternMatching"; "ms_locate_var"]))
    | ABKHyp ->
        FStar_Reflection_Builtins.pack_ln
          (FStar_Reflection_Data.Tv_FVar
             (FStar_Reflection_Builtins.pack_fv
                ["FStar"; "Tactics"; "PatternMatching"; "ms_locate_hyp"]))
    | ABKGoal ->
        FStar_Reflection_Builtins.pack_ln
          (FStar_Reflection_Data.Tv_FVar
             (FStar_Reflection_Builtins.pack_fv
                ["FStar"; "Tactics"; "PatternMatching"; "ms_locate_unit"]))
let (abspat_arg_of_abspat_argspec :
  FStar_Reflection_Types.term ->
    abspat_argspec ->
      (FStar_Reflection_Types.term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun solution_term ->
    fun argspec ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Range.mk_range "FStar.Tactics.PatternMatching.fst"
           (Prims.of_int (692)) (Prims.of_int (15)) (Prims.of_int (692))
           (Prims.of_int (56)))
        (FStar_Range.mk_range "FStar.Tactics.PatternMatching.fst"
           (Prims.of_int (692)) (Prims.of_int (59)) (Prims.of_int (693))
           (Prims.of_int (79)))
        (FStar_Tactics_Effect.lift_div_tac
           (fun uu___ -> locate_fn_of_binder_kind argspec.asa_kind))
        (fun uu___ ->
           (fun loc_fn ->
              Obj.magic
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Range.mk_range "FStar.Tactics.PatternMatching.fst"
                      (Prims.of_int (693)) (Prims.of_int (16))
                      (Prims.of_int (693)) (Prims.of_int (76)))
                   (FStar_Range.mk_range "FStar.Tactics.PatternMatching.fst"
                      (Prims.of_int (693)) (Prims.of_int (79))
                      (Prims.of_int (695)) (Prims.of_int (75)))
                   (Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (FStar_Range.mk_range
                            "FStar.Tactics.PatternMatching.fst"
                            (Prims.of_int (693)) (Prims.of_int (21))
                            (Prims.of_int (693)) (Prims.of_int (76)))
                         (FStar_Range.mk_range
                            "FStar.Tactics.PatternMatching.fst"
                            (Prims.of_int (693)) (Prims.of_int (16))
                            (Prims.of_int (693)) (Prims.of_int (76)))
                         (Obj.magic
                            (FStar_Tactics_Effect.tac_bind
                               (FStar_Range.mk_range
                                  "FStar.Tactics.PatternMatching.fst"
                                  (Prims.of_int (693)) (Prims.of_int (31))
                                  (Prims.of_int (693)) (Prims.of_int (75)))
                               (FStar_Range.mk_range
                                  "FStar.Tactics.PatternMatching.fst"
                                  (Prims.of_int (693)) (Prims.of_int (21))
                                  (Prims.of_int (693)) (Prims.of_int (76)))
                               (Obj.magic
                                  (FStar_Tactics_Effect.tac_bind
                                     (FStar_Range.mk_range
                                        "FStar.Tactics.PatternMatching.fst"
                                        (Prims.of_int (693))
                                        (Prims.of_int (41))
                                        (Prims.of_int (693))
                                        (Prims.of_int (74)))
                                     (FStar_Range.mk_range
                                        "FStar.Tactics.PatternMatching.fst"
                                        (Prims.of_int (693))
                                        (Prims.of_int (31))
                                        (Prims.of_int (693))
                                        (Prims.of_int (75)))
                                     (Obj.magic
                                        (FStar_Tactics_Derived.name_of_binder
                                           argspec.asa_name))
                                     (fun uu___ ->
                                        FStar_Tactics_Effect.lift_div_tac
                                          (fun uu___1 ->
                                             FStar_Reflection_Data.C_String
                                               uu___))))
                               (fun uu___ ->
                                  FStar_Tactics_Effect.lift_div_tac
                                    (fun uu___1 ->
                                       FStar_Reflection_Data.Tv_Const uu___))))
                         (fun uu___ ->
                            (fun uu___ ->
                               Obj.magic (FStar_Tactics_Builtins.pack uu___))
                              uu___)))
                   (fun uu___ ->
                      (fun name_tm ->
                         Obj.magic
                           (FStar_Tactics_Effect.tac_bind
                              (FStar_Range.mk_range
                                 "FStar.Tactics.PatternMatching.fst"
                                 (Prims.of_int (694)) (Prims.of_int (20))
                                 (Prims.of_int (695)) (Prims.of_int (72)))
                              (FStar_Range.mk_range
                                 "FStar.Tactics.PatternMatching.fst"
                                 (Prims.of_int (696)) (Prims.of_int (2))
                                 (Prims.of_int (696)) (Prims.of_int (27)))
                              (Obj.magic
                                 (FStar_Tactics_Effect.tac_bind
                                    (FStar_Range.mk_range
                                       "FStar.Tactics.PatternMatching.fst"
                                       (Prims.of_int (694))
                                       (Prims.of_int (21))
                                       (Prims.of_int (694))
                                       (Prims.of_int (75)))
                                    (FStar_Range.mk_range
                                       "FStar.Tactics.PatternMatching.fst"
                                       (Prims.of_int (694))
                                       (Prims.of_int (20))
                                       (Prims.of_int (695))
                                       (Prims.of_int (72)))
                                    (Obj.magic
                                       (FStar_Tactics_Effect.tac_bind
                                          (FStar_Range.mk_range
                                             "FStar.Tactics.PatternMatching.fst"
                                             (Prims.of_int (694))
                                             (Prims.of_int (22))
                                             (Prims.of_int (694))
                                             (Prims.of_int (62)))
                                          (FStar_Range.mk_range
                                             "FStar.Tactics.PatternMatching.fst"
                                             (Prims.of_int (694))
                                             (Prims.of_int (21))
                                             (Prims.of_int (694))
                                             (Prims.of_int (75)))
                                          (Obj.magic
                                             (arg_type_of_binder_kind
                                                argspec.asa_kind))
                                          (fun uu___ ->
                                             FStar_Tactics_Effect.lift_div_tac
                                               (fun uu___1 ->
                                                  (uu___,
                                                    FStar_Reflection_Data.Q_Explicit)))))
                                    (fun uu___ ->
                                       FStar_Tactics_Effect.lift_div_tac
                                         (fun uu___1 ->
                                            [uu___;
                                            (solution_term,
                                              FStar_Reflection_Data.Q_Explicit);
                                            (name_tm,
                                              FStar_Reflection_Data.Q_Explicit)]))))
                              (fun locate_args ->
                                 FStar_Tactics_Effect.lift_div_tac
                                   (fun uu___ ->
                                      FStar_Reflection_Derived.mk_app loc_fn
                                        locate_args)))) uu___))) uu___)
let rec (hoist_and_apply :
  FStar_Reflection_Types.term ->
    FStar_Reflection_Types.term Prims.list ->
      FStar_Reflection_Data.argv Prims.list ->
        (FStar_Reflection_Types.term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___2 ->
    fun uu___1 ->
      fun uu___ ->
        (fun head ->
           fun arg_terms ->
             fun hoisted_args ->
               match arg_terms with
               | [] ->
                   Obj.magic
                     (Obj.repr
                        (FStar_Tactics_Effect.lift_div_tac
                           (fun uu___ ->
                              FStar_Reflection_Derived.mk_app head
                                (FStar_List_Tot_Base.rev hoisted_args))))
               | arg_term::rest ->
                   Obj.magic
                     (Obj.repr
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Range.mk_range
                              "FStar.Tactics.PatternMatching.fst"
                              (Prims.of_int (707)) (Prims.of_int (12))
                              (Prims.of_int (707)) (Prims.of_int (40)))
                           (FStar_Range.mk_range
                              "FStar.Tactics.PatternMatching.fst"
                              (Prims.of_int (707)) (Prims.of_int (43))
                              (Prims.of_int (708)) (Prims.of_int (56)))
                           (FStar_Tactics_Effect.lift_div_tac
                              (fun uu___ ->
                                 FStar_List_Tot_Base.length hoisted_args))
                           (fun uu___ ->
                              (fun n ->
                                 Obj.magic
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Range.mk_range
                                         "FStar.Tactics.PatternMatching.fst"
                                         (Prims.of_int (708))
                                         (Prims.of_int (13))
                                         (Prims.of_int (708))
                                         (Prims.of_int (53)))
                                      (FStar_Range.mk_range
                                         "FStar.Tactics.PatternMatching.fst"
                                         (Prims.of_int (709))
                                         (Prims.of_int (4))
                                         (Prims.of_int (709))
                                         (Prims.of_int (131)))
                                      (Obj.magic
                                         (FStar_Tactics_Builtins.fresh_bv_named
                                            (Prims.strcat "x"
                                               (Prims.string_of_int n))))
                                      (fun uu___ ->
                                         (fun bv ->
                                            Obj.magic
                                              (FStar_Tactics_Effect.tac_bind
                                                 (FStar_Range.mk_range
                                                    "FStar.Tactics.PatternMatching.fst"
                                                    (Prims.of_int (709))
                                                    (Prims.of_int (9))
                                                    (Prims.of_int (709))
                                                    (Prims.of_int (131)))
                                                 (FStar_Range.mk_range
                                                    "FStar.Tactics.PatternMatching.fst"
                                                    (Prims.of_int (709))
                                                    (Prims.of_int (4))
                                                    (Prims.of_int (709))
                                                    (Prims.of_int (131)))
                                                 (Obj.magic
                                                    (FStar_Tactics_Effect.tac_bind
                                                       (FStar_Range.mk_range
                                                          "FStar.Tactics.PatternMatching.fst"
                                                          (Prims.of_int (709))
                                                          (Prims.of_int (29))
                                                          (Prims.of_int (709))
                                                          (Prims.of_int (46)))
                                                       (FStar_Range.mk_range
                                                          "FStar.Tactics.PatternMatching.fst"
                                                          (Prims.of_int (709))
                                                          (Prims.of_int (9))
                                                          (Prims.of_int (709))
                                                          (Prims.of_int (131)))
                                                       (Obj.magic
                                                          (FStar_Tactics_Builtins.pack
                                                             FStar_Reflection_Data.Tv_Unknown))
                                                       (fun uu___ ->
                                                          (fun uu___ ->
                                                             Obj.magic
                                                               (FStar_Tactics_Effect.tac_bind
                                                                  (FStar_Range.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (709))
                                                                    (Prims.of_int (56))
                                                                    (Prims.of_int (709))
                                                                    (Prims.of_int (130)))
                                                                  (FStar_Range.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (709))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (709))
                                                                    (Prims.of_int (131)))
                                                                  (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (709))
                                                                    (Prims.of_int (83))
                                                                    (Prims.of_int (709))
                                                                    (Prims.of_int (129)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (709))
                                                                    (Prims.of_int (56))
                                                                    (Prims.of_int (709))
                                                                    (Prims.of_int (130)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (709))
                                                                    (Prims.of_int (84))
                                                                    (Prims.of_int (709))
                                                                    (Prims.of_int (114)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (709))
                                                                    (Prims.of_int (83))
                                                                    (Prims.of_int (709))
                                                                    (Prims.of_int (129)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (709))
                                                                    (Prims.of_int (85))
                                                                    (Prims.of_int (709))
                                                                    (Prims.of_int (101)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (709))
                                                                    (Prims.of_int (84))
                                                                    (Prims.of_int (709))
                                                                    (Prims.of_int (114)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Builtins.pack
                                                                    (FStar_Reflection_Data.Tv_Var
                                                                    bv)))
                                                                    (fun
                                                                    uu___1 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    (uu___1,
                                                                    FStar_Reflection_Data.Q_Explicit)))))
                                                                    (fun
                                                                    uu___1 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    uu___1 ::
                                                                    hoisted_args))))
                                                                    (fun
                                                                    uu___1 ->
                                                                    (fun
                                                                    uu___1 ->
                                                                    Obj.magic
                                                                    (hoist_and_apply
                                                                    head rest
                                                                    uu___1))
                                                                    uu___1)))
                                                                  (fun uu___1
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Reflection_Data.Tv_Let
                                                                    (false,
                                                                    [], bv,
                                                                    uu___,
                                                                    arg_term,
                                                                    uu___1)))))
                                                            uu___)))
                                                 (fun uu___ ->
                                                    (fun uu___ ->
                                                       Obj.magic
                                                         (FStar_Tactics_Builtins.pack
                                                            uu___)) uu___)))
                                           uu___))) uu___)))) uu___2 uu___1
          uu___
let (specialize_abspat_continuation' :
  abspat_continuation ->
    FStar_Reflection_Types.term ->
      (FStar_Reflection_Types.term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun continuation ->
    fun solution_term ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Range.mk_range "FStar.Tactics.PatternMatching.fst"
           (Prims.of_int (715)) (Prims.of_int (4)) (Prims.of_int (715))
           (Prims.of_int (54)))
        (FStar_Range.mk_range "FStar.Tactics.PatternMatching.fst"
           (Prims.of_int (715)) (Prims.of_int (57)) (Prims.of_int (716))
           (Prims.of_int (38)))
        (FStar_Tactics_Effect.lift_div_tac
           (fun uu___ ->
              fun argspec ->
                abspat_arg_of_abspat_argspec solution_term argspec))
        (fun uu___ ->
           (fun mk_arg_term ->
              Obj.magic
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Range.mk_range "FStar.Tactics.PatternMatching.fst"
                      (Prims.of_int (716)) (Prims.of_int (23))
                      (Prims.of_int (716)) (Prims.of_int (35)))
                   (FStar_Range.mk_range "FStar.Tactics.PatternMatching.fst"
                      (Prims.of_int (715)) (Prims.of_int (57))
                      (Prims.of_int (716)) (Prims.of_int (38)))
                   (FStar_Tactics_Effect.lift_div_tac
                      (fun uu___ -> continuation))
                   (fun uu___ ->
                      (fun uu___ ->
                         match uu___ with
                         | (argspecs, body) ->
                             Obj.magic
                               (FStar_Tactics_Effect.tac_bind
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.PatternMatching.fst"
                                     (Prims.of_int (717)) (Prims.of_int (23))
                                     (Prims.of_int (717)) (Prims.of_int (49)))
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.PatternMatching.fst"
                                     (Prims.of_int (717)) (Prims.of_int (2))
                                     (Prims.of_int (717)) (Prims.of_int (52)))
                                  (Obj.magic
                                     (FStar_Tactics_Util.map mk_arg_term
                                        argspecs))
                                  (fun uu___1 ->
                                     (fun uu___1 ->
                                        Obj.magic
                                          (hoist_and_apply body uu___1 []))
                                       uu___1))) uu___))) uu___)
let (specialize_abspat_continuation :
  abspat_continuation ->
    (FStar_Reflection_Types.term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun continuation ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Range.mk_range "FStar.Tactics.PatternMatching.fst"
         (Prims.of_int (724)) (Prims.of_int (24)) (Prims.of_int (724))
         (Prims.of_int (57)))
      (FStar_Range.mk_range "FStar.Tactics.PatternMatching.fst"
         (Prims.of_int (724)) (Prims.of_int (60)) (Prims.of_int (725))
         (Prims.of_int (69)))
      (Obj.magic
         (FStar_Tactics_Derived.fresh_binder
            (FStar_Reflection_Builtins.pack_ln
               (FStar_Reflection_Data.Tv_FVar
                  (FStar_Reflection_Builtins.pack_fv
                     ["FStar";
                     "Tactics";
                     "PatternMatching";
                     "matching_solution"])))))
      (fun uu___ ->
         (fun solution_binder ->
            Obj.magic
              (FStar_Tactics_Effect.tac_bind
                 (FStar_Range.mk_range "FStar.Tactics.PatternMatching.fst"
                    (Prims.of_int (725)) (Prims.of_int (22))
                    (Prims.of_int (725)) (Prims.of_int (66)))
                 (FStar_Range.mk_range "FStar.Tactics.PatternMatching.fst"
                    (Prims.of_int (725)) (Prims.of_int (69))
                    (Prims.of_int (726)) (Prims.of_int (77)))
                 (Obj.magic
                    (FStar_Tactics_Builtins.pack
                       (FStar_Reflection_Data.Tv_Var
                          (FStar_Reflection_Derived.bv_of_binder
                             solution_binder))))
                 (fun uu___ ->
                    (fun solution_term ->
                       Obj.magic
                         (FStar_Tactics_Effect.tac_bind
                            (FStar_Range.mk_range
                               "FStar.Tactics.PatternMatching.fst"
                               (Prims.of_int (726)) (Prims.of_int (16))
                               (Prims.of_int (726)) (Prims.of_int (74)))
                            (FStar_Range.mk_range
                               "FStar.Tactics.PatternMatching.fst"
                               (Prims.of_int (726)) (Prims.of_int (77))
                               (Prims.of_int (727)) (Prims.of_int (56)))
                            (Obj.magic
                               (specialize_abspat_continuation' continuation
                                  solution_term))
                            (fun uu___ ->
                               (fun applied ->
                                  Obj.magic
                                    (FStar_Tactics_Effect.tac_bind
                                       (FStar_Range.mk_range
                                          "FStar.Tactics.PatternMatching.fst"
                                          (Prims.of_int (727))
                                          (Prims.of_int (16))
                                          (Prims.of_int (727))
                                          (Prims.of_int (53)))
                                       (FStar_Range.mk_range
                                          "FStar.Tactics.PatternMatching.fst"
                                          (Prims.of_int (728))
                                          (Prims.of_int (2))
                                          (Prims.of_int (731))
                                          (Prims.of_int (9)))
                                       (Obj.magic
                                          (FStar_Tactics_Builtins.pack
                                             (FStar_Reflection_Data.Tv_Abs
                                                (solution_binder, applied))))
                                       (fun uu___ ->
                                          (fun thunked ->
                                             Obj.magic
                                               (FStar_Tactics_Effect.tac_bind
                                                  (FStar_Range.mk_range
                                                     "FStar.Tactics.PatternMatching.fst"
                                                     (Prims.of_int (728))
                                                     (Prims.of_int (2))
                                                     (Prims.of_int (728))
                                                     (Prims.of_int (56)))
                                                  (FStar_Range.mk_range
                                                     "FStar.Tactics.PatternMatching.fst"
                                                     (Prims.of_int (728))
                                                     (Prims.of_int (57))
                                                     (Prims.of_int (729))
                                                     (Prims.of_int (41)))
                                                  (Obj.magic
                                                     (FStar_Tactics_Effect.tac_bind
                                                        (FStar_Range.mk_range
                                                           "FStar.Tactics.PatternMatching.fst"
                                                           (Prims.of_int (728))
                                                           (Prims.of_int (8))
                                                           (Prims.of_int (728))
                                                           (Prims.of_int (56)))
                                                        (FStar_Range.mk_range
                                                           "FStar.Tactics.PatternMatching.fst"
                                                           (Prims.of_int (728))
                                                           (Prims.of_int (2))
                                                           (Prims.of_int (728))
                                                           (Prims.of_int (56)))
                                                        (Obj.magic
                                                           (FStar_Tactics_Effect.tac_bind
                                                              (FStar_Range.mk_range
                                                                 "FStar.Tactics.PatternMatching.fst"
                                                                 (Prims.of_int (728))
                                                                 (Prims.of_int (31))
                                                                 (Prims.of_int (728))
                                                                 (Prims.of_int (55)))
                                                              (FStar_Range.mk_range
                                                                 "prims.fst"
                                                                 (Prims.of_int (590))
                                                                 (Prims.of_int (19))
                                                                 (Prims.of_int (590))
                                                                 (Prims.of_int (31)))
                                                              (Obj.magic
                                                                 (FStar_Tactics_Builtins.term_to_string
                                                                    thunked))
                                                              (fun uu___ ->
                                                                 FStar_Tactics_Effect.lift_div_tac
                                                                   (fun
                                                                    uu___1 ->
                                                                    Prims.strcat
                                                                    "Specialized into "
                                                                    uu___))))
                                                        (fun uu___ ->
                                                           (fun uu___ ->
                                                              Obj.magic
                                                                (debug uu___))
                                                             uu___)))
                                                  (fun uu___ ->
                                                     (fun uu___ ->
                                                        Obj.magic
                                                          (FStar_Tactics_Effect.tac_bind
                                                             (FStar_Range.mk_range
                                                                "FStar.Tactics.PatternMatching.fst"
                                                                (Prims.of_int (729))
                                                                (Prims.of_int (19))
                                                                (Prims.of_int (729))
                                                                (Prims.of_int (38)))
                                                             (FStar_Range.mk_range
                                                                "FStar.Tactics.PatternMatching.fst"
                                                                (Prims.of_int (730))
                                                                (Prims.of_int (2))
                                                                (Prims.of_int (731))
                                                                (Prims.of_int (9)))
                                                             (Obj.magic
                                                                (beta_reduce
                                                                   thunked))
                                                             (fun uu___1 ->
                                                                (fun
                                                                   normalized
                                                                   ->
                                                                   Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (730))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (730))
                                                                    (Prims.of_int (61)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (727))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (727))
                                                                    (Prims.of_int (13)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (730))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (730))
                                                                    (Prims.of_int (61)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (730))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (730))
                                                                    (Prims.of_int (61)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (730))
                                                                    (Prims.of_int (33))
                                                                    (Prims.of_int (730))
                                                                    (Prims.of_int (60)))
                                                                    (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (31)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Builtins.term_to_string
                                                                    normalized))
                                                                    (fun
                                                                    uu___1 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    Prims.strcat
                                                                    "\226\128\166 which reduces to "
                                                                    uu___1))))
                                                                    (fun
                                                                    uu___1 ->
                                                                    (fun
                                                                    uu___1 ->
                                                                    Obj.magic
                                                                    (debug
                                                                    uu___1))
                                                                    uu___1)))
                                                                    (fun
                                                                    uu___1 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    thunked))))
                                                                  uu___1)))
                                                       uu___))) uu___)))
                                 uu___))) uu___))) uu___)
let interp_abspat_continuation :
  'a .
    abspat_continuation ->
      (matching_solution -> ('a, unit) FStar_Tactics_Effect.tac_repr, 
        unit) FStar_Tactics_Effect.tac_repr
  =
  fun continuation ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Range.mk_range "FStar.Tactics.PatternMatching.fst"
         (Prims.of_int (738)) (Prims.of_int (16)) (Prims.of_int (738))
         (Prims.of_int (59)))
      (FStar_Range.mk_range "FStar.Tactics.PatternMatching.fst"
         (Prims.of_int (739)) (Prims.of_int (2)) (Prims.of_int (739))
         (Prims.of_int (47)))
      (Obj.magic (specialize_abspat_continuation continuation))
      (fun uu___ ->
         (fun applied -> Obj.magic (FStar_Tactics_Builtins.unquote applied))
           uu___)
let interp_abspat :
  'a .
    'a ->
      ((matching_problem * abspat_continuation), unit)
        FStar_Tactics_Effect.tac_repr
  =
  fun abspat ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Range.mk_range "FStar.Tactics.PatternMatching.fst"
         (Prims.of_int (749)) (Prims.of_int (26)) (Prims.of_int (749))
         (Prims.of_int (40)))
      (FStar_Range.mk_range "FStar.Tactics.PatternMatching.fst"
         (Prims.of_int (749)) (Prims.of_int (2)) (Prims.of_int (749))
         (Prims.of_int (40)))
      (FStar_Tactics_Effect.lift_div_tac
         (fun uu___ ->
            (fun uu___ ->
               Obj.magic
                 (failwith "Cannot evaluate open quotation at runtime"))
              uu___))
      (fun uu___ ->
         (fun uu___ -> Obj.magic (matching_problem_of_abs uu___)) uu___)
let match_abspat :
  'b 'a .
    'a ->
      (abspat_continuation ->
         (matching_solution -> ('b, unit) FStar_Tactics_Effect.tac_repr,
           unit) FStar_Tactics_Effect.tac_repr)
        -> ('b, unit) FStar_Tactics_Effect.tac_repr
  =
  fun abspat ->
    fun k ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Range.mk_range "FStar.Tactics.PatternMatching.fst"
           (Prims.of_int (757)) (Prims.of_int (13)) (Prims.of_int (757))
           (Prims.of_int (24)))
        (FStar_Range.mk_range "FStar.Tactics.PatternMatching.fst"
           (Prims.of_int (757)) (Prims.of_int (27)) (Prims.of_int (758))
           (Prims.of_int (49)))
        (Obj.magic (FStar_Tactics_Derived.cur_goal ()))
        (fun uu___ ->
           (fun goal ->
              Obj.magic
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Range.mk_range "FStar.Tactics.PatternMatching.fst"
                      (Prims.of_int (758)) (Prims.of_int (19))
                      (Prims.of_int (758)) (Prims.of_int (46)))
                   (FStar_Range.mk_range "FStar.Tactics.PatternMatching.fst"
                      (Prims.of_int (758)) (Prims.of_int (49))
                      (Prims.of_int (759)) (Prims.of_int (53)))
                   (Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (FStar_Range.mk_range
                            "FStar.Tactics.PatternMatching.fst"
                            (Prims.of_int (758)) (Prims.of_int (34))
                            (Prims.of_int (758)) (Prims.of_int (46)))
                         (FStar_Range.mk_range
                            "FStar.Tactics.PatternMatching.fst"
                            (Prims.of_int (758)) (Prims.of_int (19))
                            (Prims.of_int (758)) (Prims.of_int (46)))
                         (Obj.magic (FStar_Tactics_Derived.cur_env ()))
                         (fun uu___ ->
                            FStar_Tactics_Effect.lift_div_tac
                              (fun uu___1 ->
                                 FStar_Reflection_Builtins.binders_of_env
                                   uu___))))
                   (fun uu___ ->
                      (fun hypotheses ->
                         Obj.magic
                           (FStar_Tactics_Effect.tac_bind
                              (FStar_Range.mk_range
                                 "FStar.Tactics.PatternMatching.fst"
                                 (Prims.of_int (759)) (Prims.of_int (30))
                                 (Prims.of_int (759)) (Prims.of_int (50)))
                              (FStar_Range.mk_range
                                 "FStar.Tactics.PatternMatching.fst"
                                 (Prims.of_int (758)) (Prims.of_int (49))
                                 (Prims.of_int (759)) (Prims.of_int (53)))
                              (Obj.magic (interp_abspat abspat))
                              (fun uu___ ->
                                 (fun uu___ ->
                                    match uu___ with
                                    | (problem, continuation) ->
                                        Obj.magic
                                          (FStar_Tactics_Effect.tac_bind
                                             (FStar_Range.mk_range
                                                "FStar.Tactics.PatternMatching.fst"
                                                (Prims.of_int (760))
                                                (Prims.of_int (35))
                                                (Prims.of_int (760))
                                                (Prims.of_int (51)))
                                             (FStar_Range.mk_range
                                                "FStar.Tactics.PatternMatching.fst"
                                                (Prims.of_int (760))
                                                (Prims.of_int (2))
                                                (Prims.of_int (760))
                                                (Prims.of_int (51)))
                                             (Obj.magic (k continuation))
                                             (fun uu___1 ->
                                                (fun uu___1 ->
                                                   Obj.magic
                                                     (solve_mp problem
                                                        hypotheses goal
                                                        uu___1)) uu___1)))
                                   uu___))) uu___))) uu___)
let inspect_abspat_problem :
  'a . 'a -> (matching_problem, unit) FStar_Tactics_Effect.tac_repr =
  fun abspat ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Range.mk_range "FStar.Tactics.PatternMatching.fst"
         (Prims.of_int (764)) (Prims.of_int (6)) (Prims.of_int (764))
         (Prims.of_int (31)))
      (FStar_Range.mk_range "FStar.Tactics.PatternMatching.fst"
         (Prims.of_int (764)) (Prims.of_int (2)) (Prims.of_int (764))
         (Prims.of_int (31))) (Obj.magic (interp_abspat abspat))
      (fun uu___ ->
         FStar_Tactics_Effect.lift_div_tac
           (fun uu___1 -> FStar_Pervasives_Native.fst uu___))
let inspect_abspat_solution :
  'a . 'a -> (matching_solution, unit) FStar_Tactics_Effect.tac_repr =
  fun abspat ->
    match_abspat abspat
      (fun uu___ ->
         (fun uu___ ->
            Obj.magic
              (FStar_Tactics_Effect.lift_div_tac
                 (fun uu___2 ->
                    fun uu___1 ->
                      (fun uu___1 ->
                         fun solution ->
                           Obj.magic
                             (FStar_Tactics_Effect.lift_div_tac
                                (fun uu___2 -> solution))) uu___2 uu___1)))
           uu___)
let tpair :
  'a 'b .
    'a ->
      ('b -> (('a * 'b), unit) FStar_Tactics_Effect.tac_repr, unit)
        FStar_Tactics_Effect.tac_repr
  =
  fun uu___ ->
    (fun x ->
       Obj.magic
         (FStar_Tactics_Effect.lift_div_tac
            (fun uu___1 ->
               fun uu___ ->
                 (fun uu___ ->
                    fun y ->
                      Obj.magic
                        (FStar_Tactics_Effect.lift_div_tac
                           (fun uu___1 -> (x, y)))) uu___1 uu___))) uu___
let gpm : 'b 'a . 'a -> unit -> ('b, unit) FStar_Tactics_Effect.tac_repr =
  fun abspat ->
    fun uu___ ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Range.mk_range "FStar.Tactics.PatternMatching.fst"
           (Prims.of_int (788)) (Prims.of_int (31)) (Prims.of_int (788))
           (Prims.of_int (56)))
        (FStar_Range.mk_range "FStar.Tactics.PatternMatching.fst"
           (Prims.of_int (787)) (Prims.of_int (38)) (Prims.of_int (788))
           (Prims.of_int (59))) (Obj.magic (match_abspat abspat tpair))
        (fun uu___1 ->
           (fun uu___1 ->
              match uu___1 with
              | (continuation, solution) ->
                  Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Range.mk_range
                          "FStar.Tactics.PatternMatching.fst"
                          (Prims.of_int (789)) (Prims.of_int (2))
                          (Prims.of_int (789)) (Prims.of_int (52)))
                       (FStar_Range.mk_range
                          "FStar.Tactics.PatternMatching.fst"
                          (Prims.of_int (789)) (Prims.of_int (2))
                          (Prims.of_int (789)) (Prims.of_int (52)))
                       (Obj.magic (interp_abspat_continuation continuation))
                       (fun uu___2 ->
                          (fun uu___2 -> Obj.magic (uu___2 solution)) uu___2)))
             uu___1)
let pm : 'b 'a . 'a -> ('b, unit) FStar_Tactics_Effect.tac_repr =
  fun abspat -> match_abspat abspat interp_abspat_continuation
let fetch_eq_side' :
  'a . unit -> (FStar_Reflection_Types.term * FStar_Reflection_Types.term) =
  fun uu___ ->
    (fun uu___ ->
       Obj.magic
         (gpm
            (fun left ->
               fun right ->
                 fun g ->
                   FStar_Tactics_Effect.tac_bind
                     (FStar_Range.mk_range
                        "FStar.Tactics.PatternMatching.fst"
                        (Prims.of_int (812)) (Prims.of_int (10))
                        (Prims.of_int (812)) (Prims.of_int (20)))
                     (FStar_Range.mk_range
                        "FStar.Tactics.PatternMatching.fst"
                        (Prims.of_int (812)) (Prims.of_int (9))
                        (Prims.of_int (812)) (Prims.of_int (34)))
                     (FStar_Tactics_Effect.lift_div_tac
                        (fun uu___1 ->
                           (fun uu___1 ->
                              Obj.magic
                                (failwith
                                   "Cannot evaluate open quotation at runtime"))
                             uu___1))
                     (fun uu___1 ->
                        (fun uu___1 ->
                           Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Range.mk_range
                                   "FStar.Tactics.PatternMatching.fst"
                                   (Prims.of_int (812)) (Prims.of_int (22))
                                   (Prims.of_int (812)) (Prims.of_int (33)))
                                (FStar_Range.mk_range
                                   "FStar.Tactics.PatternMatching.fst"
                                   (Prims.of_int (812)) (Prims.of_int (9))
                                   (Prims.of_int (812)) (Prims.of_int (34)))
                                (FStar_Tactics_Effect.lift_div_tac
                                   (fun uu___2 ->
                                      (fun uu___2 ->
                                         Obj.magic
                                           (failwith
                                              "Cannot evaluate open quotation at runtime"))
                                        uu___2))
                                (fun uu___2 ->
                                   FStar_Tactics_Effect.lift_div_tac
                                     (fun uu___3 -> (uu___1, uu___2)))))
                          uu___1)) ())) uu___