open Prims
let (fetch_eq_side :
  unit ->
    ((FStar_Tactics_NamedView.term * FStar_Tactics_NamedView.term), unit)
      FStar_Tactics_Effect.tac_repr)
  =
  fun uu___ ->
    let uu___1 = FStar_Tactics_V2_Derived.cur_goal () in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.PatternMatching.fst"
               (Prims.of_int (63)) (Prims.of_int (10)) (Prims.of_int (63))
               (Prims.of_int (21)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.PatternMatching.fst"
               (Prims.of_int (64)) (Prims.of_int (2)) (Prims.of_int (88))
               (Prims.of_int (39))))) (Obj.magic uu___1)
      (fun uu___2 ->
         (fun g ->
            let uu___2 = FStar_Tactics_NamedView.inspect g in
            Obj.magic
              (FStar_Tactics_Effect.tac_bind
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range
                          "FStar.Tactics.PatternMatching.fst"
                          (Prims.of_int (64)) (Prims.of_int (8))
                          (Prims.of_int (64)) (Prims.of_int (17)))))
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range
                          "FStar.Tactics.PatternMatching.fst"
                          (Prims.of_int (64)) (Prims.of_int (2))
                          (Prims.of_int (88)) (Prims.of_int (39)))))
                 (Obj.magic uu___2)
                 (fun uu___3 ->
                    (fun uu___3 ->
                       match uu___3 with
                       | FStar_Tactics_NamedView.Tv_App
                           (squash, (g1, uu___4)) ->
                           Obj.magic
                             (Obj.repr
                                (let uu___5 =
                                   FStar_Tactics_NamedView.inspect squash in
                                 FStar_Tactics_Effect.tac_bind
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "FStar.Tactics.PatternMatching.fst"
                                            (Prims.of_int (66))
                                            (Prims.of_int (11))
                                            (Prims.of_int (66))
                                            (Prims.of_int (25)))))
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "FStar.Tactics.PatternMatching.fst"
                                            (Prims.of_int (66))
                                            (Prims.of_int (4))
                                            (Prims.of_int (87))
                                            (Prims.of_int (51)))))
                                   (Obj.magic uu___5)
                                   (fun uu___6 ->
                                      (fun uu___6 ->
                                         match uu___6 with
                                         | FStar_Tactics_NamedView.Tv_UInst
                                             (squash1, uu___7) ->
                                             Obj.magic
                                               (Obj.repr
                                                  (if
                                                     (FStar_Reflection_V2_Derived.fv_to_string
                                                        squash1)
                                                       =
                                                       (FStar_Reflection_V2_Derived.flatten_name
                                                          FStar_Reflection_Const.squash_qn)
                                                   then
                                                     Obj.repr
                                                       (let uu___8 =
                                                          FStar_Tactics_NamedView.inspect
                                                            g1 in
                                                        FStar_Tactics_Effect.tac_bind
                                                          (FStar_Sealed.seal
                                                             (Obj.magic
                                                                (FStar_Range.mk_range
                                                                   "FStar.Tactics.PatternMatching.fst"
                                                                   (Prims.of_int (70))
                                                                   (Prims.of_int (16))
                                                                   (Prims.of_int (70))
                                                                   (Prims.of_int (25)))))
                                                          (FStar_Sealed.seal
                                                             (Obj.magic
                                                                (FStar_Range.mk_range
                                                                   "FStar.Tactics.PatternMatching.fst"
                                                                   (Prims.of_int (70))
                                                                   (Prims.of_int (9))
                                                                   (Prims.of_int (85))
                                                                   (Prims.of_int (48)))))
                                                          (Obj.magic uu___8)
                                                          (fun uu___9 ->
                                                             (fun uu___9 ->
                                                                match uu___9
                                                                with
                                                                | FStar_Tactics_NamedView.Tv_App
                                                                    (eq_type_x,
                                                                    (y,
                                                                    uu___10))
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (let uu___11
                                                                    =
                                                                    FStar_Tactics_NamedView.inspect
                                                                    eq_type_x in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (72))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (72))
                                                                    (Prims.of_int (36)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (72))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (84))
                                                                    (Prims.of_int (39)))))
                                                                    (Obj.magic
                                                                    uu___11)
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    match uu___12
                                                                    with
                                                                    | 
                                                                    FStar_Tactics_NamedView.Tv_App
                                                                    (eq_type,
                                                                    (x,
                                                                    uu___13))
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (let uu___14
                                                                    =
                                                                    FStar_Tactics_NamedView.inspect
                                                                    eq_type in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (74))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (74))
                                                                    (Prims.of_int (37)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (74))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (83))
                                                                    (Prims.of_int (42)))))
                                                                    (Obj.magic
                                                                    uu___14)
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    match uu___15
                                                                    with
                                                                    | 
                                                                    FStar_Tactics_NamedView.Tv_App
                                                                    (eq,
                                                                    (typ,
                                                                    uu___16))
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (let uu___17
                                                                    =
                                                                    FStar_Tactics_NamedView.inspect
                                                                    eq in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (76))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (76))
                                                                    (Prims.of_int (35)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (76))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (82))
                                                                    (Prims.of_int (55)))))
                                                                    (Obj.magic
                                                                    uu___17)
                                                                    (fun
                                                                    uu___18
                                                                    ->
                                                                    match uu___18
                                                                    with
                                                                    | 
                                                                    FStar_Tactics_NamedView.Tv_UInst
                                                                    (eq1,
                                                                    uu___19)
                                                                    ->
                                                                    if
                                                                    (FStar_Reflection_V2_Derived.fv_to_string
                                                                    eq1) =
                                                                    (FStar_Reflection_V2_Derived.flatten_name
                                                                    FStar_Reflection_Const.eq2_qn)
                                                                    then
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___20
                                                                    -> (x, y))
                                                                    else
                                                                    FStar_Tactics_V2_Derived.fail
                                                                    "not an equality"
                                                                    | 
                                                                    FStar_Tactics_NamedView.Tv_FVar
                                                                    eq1 ->
                                                                    if
                                                                    (FStar_Reflection_V2_Derived.fv_to_string
                                                                    eq1) =
                                                                    (FStar_Reflection_V2_Derived.flatten_name
                                                                    FStar_Reflection_Const.eq2_qn)
                                                                    then
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___19
                                                                    -> (x, y))
                                                                    else
                                                                    FStar_Tactics_V2_Derived.fail
                                                                    "not an equality"
                                                                    | 
                                                                    uu___19
                                                                    ->
                                                                    FStar_Tactics_V2_Derived.fail
                                                                    "not an app2 of fvar: ")))
                                                                    | 
                                                                    uu___16
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_V2_Derived.fail
                                                                    "not an app3")))
                                                                    uu___15)))
                                                                    | 
                                                                    uu___13
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_V2_Derived.fail
                                                                    "not an app2")))
                                                                    uu___12)))
                                                                | uu___10 ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_V2_Derived.fail
                                                                    "not an app under squash")))
                                                               uu___9))
                                                   else
                                                     Obj.repr
                                                       (FStar_Tactics_V2_Derived.fail
                                                          "not a squash")))
                                         | FStar_Tactics_NamedView.Tv_FVar
                                             squash1 ->
                                             Obj.magic
                                               (Obj.repr
                                                  (if
                                                     (FStar_Reflection_V2_Derived.fv_to_string
                                                        squash1)
                                                       =
                                                       (FStar_Reflection_V2_Derived.flatten_name
                                                          FStar_Reflection_Const.squash_qn)
                                                   then
                                                     Obj.repr
                                                       (let uu___7 =
                                                          FStar_Tactics_NamedView.inspect
                                                            g1 in
                                                        FStar_Tactics_Effect.tac_bind
                                                          (FStar_Sealed.seal
                                                             (Obj.magic
                                                                (FStar_Range.mk_range
                                                                   "FStar.Tactics.PatternMatching.fst"
                                                                   (Prims.of_int (70))
                                                                   (Prims.of_int (16))
                                                                   (Prims.of_int (70))
                                                                   (Prims.of_int (25)))))
                                                          (FStar_Sealed.seal
                                                             (Obj.magic
                                                                (FStar_Range.mk_range
                                                                   "FStar.Tactics.PatternMatching.fst"
                                                                   (Prims.of_int (70))
                                                                   (Prims.of_int (9))
                                                                   (Prims.of_int (85))
                                                                   (Prims.of_int (48)))))
                                                          (Obj.magic uu___7)
                                                          (fun uu___8 ->
                                                             (fun uu___8 ->
                                                                match uu___8
                                                                with
                                                                | FStar_Tactics_NamedView.Tv_App
                                                                    (eq_type_x,
                                                                    (y,
                                                                    uu___9))
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (let uu___10
                                                                    =
                                                                    FStar_Tactics_NamedView.inspect
                                                                    eq_type_x in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (72))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (72))
                                                                    (Prims.of_int (36)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (72))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (84))
                                                                    (Prims.of_int (39)))))
                                                                    (Obj.magic
                                                                    uu___10)
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    match uu___11
                                                                    with
                                                                    | 
                                                                    FStar_Tactics_NamedView.Tv_App
                                                                    (eq_type,
                                                                    (x,
                                                                    uu___12))
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (let uu___13
                                                                    =
                                                                    FStar_Tactics_NamedView.inspect
                                                                    eq_type in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (74))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (74))
                                                                    (Prims.of_int (37)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (74))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (83))
                                                                    (Prims.of_int (42)))))
                                                                    (Obj.magic
                                                                    uu___13)
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    match uu___14
                                                                    with
                                                                    | 
                                                                    FStar_Tactics_NamedView.Tv_App
                                                                    (eq,
                                                                    (typ,
                                                                    uu___15))
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (let uu___16
                                                                    =
                                                                    FStar_Tactics_NamedView.inspect
                                                                    eq in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (76))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (76))
                                                                    (Prims.of_int (35)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (76))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (82))
                                                                    (Prims.of_int (55)))))
                                                                    (Obj.magic
                                                                    uu___16)
                                                                    (fun
                                                                    uu___17
                                                                    ->
                                                                    match uu___17
                                                                    with
                                                                    | 
                                                                    FStar_Tactics_NamedView.Tv_UInst
                                                                    (eq1,
                                                                    uu___18)
                                                                    ->
                                                                    if
                                                                    (FStar_Reflection_V2_Derived.fv_to_string
                                                                    eq1) =
                                                                    (FStar_Reflection_V2_Derived.flatten_name
                                                                    FStar_Reflection_Const.eq2_qn)
                                                                    then
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___19
                                                                    -> (x, y))
                                                                    else
                                                                    FStar_Tactics_V2_Derived.fail
                                                                    "not an equality"
                                                                    | 
                                                                    FStar_Tactics_NamedView.Tv_FVar
                                                                    eq1 ->
                                                                    if
                                                                    (FStar_Reflection_V2_Derived.fv_to_string
                                                                    eq1) =
                                                                    (FStar_Reflection_V2_Derived.flatten_name
                                                                    FStar_Reflection_Const.eq2_qn)
                                                                    then
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___18
                                                                    -> (x, y))
                                                                    else
                                                                    FStar_Tactics_V2_Derived.fail
                                                                    "not an equality"
                                                                    | 
                                                                    uu___18
                                                                    ->
                                                                    FStar_Tactics_V2_Derived.fail
                                                                    "not an app2 of fvar: ")))
                                                                    | 
                                                                    uu___15
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_V2_Derived.fail
                                                                    "not an app3")))
                                                                    uu___14)))
                                                                    | 
                                                                    uu___12
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_V2_Derived.fail
                                                                    "not an app2")))
                                                                    uu___11)))
                                                                | uu___9 ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_V2_Derived.fail
                                                                    "not an app under squash")))
                                                               uu___8))
                                                   else
                                                     Obj.repr
                                                       (FStar_Tactics_V2_Derived.fail
                                                          "not a squash")))
                                         | uu___7 ->
                                             Obj.magic
                                               (Obj.repr
                                                  (FStar_Tactics_V2_Derived.fail
                                                     "not an app of fvar at top level")))
                                        uu___6)))
                       | uu___4 ->
                           Obj.magic
                             (Obj.repr
                                (FStar_Tactics_V2_Derived.fail
                                   "not an app at top level"))) uu___3)))
           uu___2)
let mustfail :
  'a .
    (unit -> ('a, unit) FStar_Tactics_Effect.tac_repr) ->
      Prims.string -> (unit, unit) FStar_Tactics_Effect.tac_repr
  =
  fun t ->
    fun message ->
      let uu___ = FStar_Tactics_V2_Derived.trytac t in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.PatternMatching.fst"
                 (Prims.of_int (130)) (Prims.of_int (10))
                 (Prims.of_int (130)) (Prims.of_int (18)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.PatternMatching.fst"
                 (Prims.of_int (130)) (Prims.of_int (4)) (Prims.of_int (132))
                 (Prims.of_int (16))))) (Obj.magic uu___)
        (fun uu___1 ->
           match uu___1 with
           | FStar_Pervasives_Native.Some uu___2 ->
               FStar_Tactics_V2_Derived.fail message
           | FStar_Pervasives_Native.None ->
               FStar_Tactics_Effect.lift_div_tac (fun uu___2 -> ()))
let (implies_intro' : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    let uu___1 = FStar_Tactics_V2_Logic.implies_intro () in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.PatternMatching.fst"
               (Prims.of_int (138)) (Prims.of_int (10)) (Prims.of_int (138))
               (Prims.of_int (26)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.PatternMatching.fst"
               (Prims.of_int (138)) (Prims.of_int (30)) (Prims.of_int (138))
               (Prims.of_int (32))))) (Obj.magic uu___1)
      (fun uu___2 -> FStar_Tactics_Effect.lift_div_tac (fun uu___3 -> ()))
let repeat' :
  'a .
    (unit -> ('a, unit) FStar_Tactics_Effect.tac_repr) ->
      (unit, unit) FStar_Tactics_Effect.tac_repr
  =
  fun f ->
    let uu___ = FStar_Tactics_V2_Derived.repeat f in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.PatternMatching.fst"
               (Prims.of_int (141)) (Prims.of_int (10)) (Prims.of_int (141))
               (Prims.of_int (18)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.PatternMatching.fst"
               (Prims.of_int (141)) (Prims.of_int (22)) (Prims.of_int (141))
               (Prims.of_int (24))))) (Obj.magic uu___)
      (fun uu___1 -> FStar_Tactics_Effect.lift_div_tac (fun uu___2 -> ()))
let (and_elim' :
  FStar_Tactics_NamedView.binding ->
    (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun h ->
    let uu___ =
      FStar_Tactics_V2_Logic.and_elim
        (FStar_Tactics_NamedView.pack
           (FStar_Tactics_NamedView.Tv_Var
              (FStar_Tactics_V2_SyntaxCoercions.binding_to_namedv h))) in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.PatternMatching.fst"
               (Prims.of_int (144)) (Prims.of_int (2)) (Prims.of_int (144))
               (Prims.of_int (28)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.PatternMatching.fst"
               (Prims.of_int (145)) (Prims.of_int (2)) (Prims.of_int (145))
               (Prims.of_int (9))))) (Obj.magic uu___)
      (fun uu___1 ->
         (fun uu___1 -> Obj.magic (FStarC_Tactics_V2_Builtins.clear h))
           uu___1)
let exact_hyp :
  'a .
    FStar_Tactics_NamedView.namedv ->
      (unit, unit) FStar_Tactics_Effect.tac_repr
  =
  fun h ->
    let uu___ =
      Obj.magic
        (FStar_Tactics_Effect.lift_div_tac
           (fun uu___1 ->
              (fun uu___1 ->
                 Obj.magic
                   (failwith "Cannot evaluate open quotation at runtime"))
                uu___1)) in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.PatternMatching.fst"
               (Prims.of_int (149)) (Prims.of_int (11)) (Prims.of_int (149))
               (Prims.of_int (48)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.PatternMatching.fst"
               (Prims.of_int (150)) (Prims.of_int (2)) (Prims.of_int (150))
               (Prims.of_int (53))))) (Obj.magic uu___)
      (fun uu___1 ->
         (fun hd ->
            Obj.magic
              (FStar_Tactics_V2_Derived.exact
                 (FStar_Reflection_V2_Derived.mk_app hd
                    [((FStar_Tactics_NamedView.pack
                         (FStar_Tactics_NamedView.Tv_Var h)),
                       FStarC_Reflection_V2_Data.Q_Explicit)]))) uu___1)
let (exact_hyp' :
  FStar_Tactics_NamedView.namedv ->
    (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun h ->
    FStar_Tactics_V2_Derived.exact
      (FStar_Tactics_NamedView.pack (FStar_Tactics_NamedView.Tv_Var h))
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
  | SimpleMismatch of (pattern * FStar_Tactics_NamedView.term) 
  | NonLinearMismatch of (varname * FStar_Tactics_NamedView.term *
  FStar_Tactics_NamedView.term) 
  | UnsupportedTermInPattern of FStar_Tactics_NamedView.term 
  | IncorrectTypeInAbsPatBinder of FStarC_Reflection_Types.typ 
let (uu___is_NameMismatch : match_exception -> Prims.bool) =
  fun projectee ->
    match projectee with | NameMismatch _0 -> true | uu___ -> false
let (__proj__NameMismatch__item___0 : match_exception -> (qn * qn)) =
  fun projectee -> match projectee with | NameMismatch _0 -> _0
let (uu___is_SimpleMismatch : match_exception -> Prims.bool) =
  fun projectee ->
    match projectee with | SimpleMismatch _0 -> true | uu___ -> false
let (__proj__SimpleMismatch__item___0 :
  match_exception -> (pattern * FStar_Tactics_NamedView.term)) =
  fun projectee -> match projectee with | SimpleMismatch _0 -> _0
let (uu___is_NonLinearMismatch : match_exception -> Prims.bool) =
  fun projectee ->
    match projectee with | NonLinearMismatch _0 -> true | uu___ -> false
let (__proj__NonLinearMismatch__item___0 :
  match_exception ->
    (varname * FStar_Tactics_NamedView.term * FStar_Tactics_NamedView.term))
  = fun projectee -> match projectee with | NonLinearMismatch _0 -> _0
let (uu___is_UnsupportedTermInPattern : match_exception -> Prims.bool) =
  fun projectee ->
    match projectee with
    | UnsupportedTermInPattern _0 -> true
    | uu___ -> false
let (__proj__UnsupportedTermInPattern__item___0 :
  match_exception -> FStar_Tactics_NamedView.term) =
  fun projectee -> match projectee with | UnsupportedTermInPattern _0 -> _0
let (uu___is_IncorrectTypeInAbsPatBinder : match_exception -> Prims.bool) =
  fun projectee ->
    match projectee with
    | IncorrectTypeInAbsPatBinder _0 -> true
    | uu___ -> false
let (__proj__IncorrectTypeInAbsPatBinder__item___0 :
  match_exception -> FStarC_Reflection_Types.typ) =
  fun projectee ->
    match projectee with | IncorrectTypeInAbsPatBinder _0 -> _0
let (term_head :
  FStar_Tactics_NamedView.term ->
    (Prims.string, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    let uu___ = FStar_Tactics_NamedView.inspect t in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.PatternMatching.fst"
               (Prims.of_int (203)) (Prims.of_int (8)) (Prims.of_int (203))
               (Prims.of_int (17)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.PatternMatching.fst"
               (Prims.of_int (203)) (Prims.of_int (2)) (Prims.of_int (220))
               (Prims.of_int (28))))) (Obj.magic uu___)
      (fun uu___1 ->
         FStar_Tactics_Effect.lift_div_tac
           (fun uu___2 ->
              match uu___1 with
              | FStar_Tactics_NamedView.Tv_Var bv -> "Tv_Var"
              | FStar_Tactics_NamedView.Tv_BVar fv -> "Tv_BVar"
              | FStar_Tactics_NamedView.Tv_FVar fv -> "Tv_FVar"
              | FStar_Tactics_NamedView.Tv_UInst (uu___3, uu___4) ->
                  "Tv_UInst"
              | FStar_Tactics_NamedView.Tv_App (f, x) -> "Tv_App"
              | FStar_Tactics_NamedView.Tv_Abs (x, t1) -> "Tv_Abs"
              | FStar_Tactics_NamedView.Tv_Arrow (x, t1) -> "Tv_Arrow"
              | FStar_Tactics_NamedView.Tv_Type uu___3 -> "Tv_Type"
              | FStar_Tactics_NamedView.Tv_Refine (x, t1) -> "Tv_Refine"
              | FStar_Tactics_NamedView.Tv_Const cst -> "Tv_Const"
              | FStar_Tactics_NamedView.Tv_Uvar (i, t1) -> "Tv_Uvar"
              | FStar_Tactics_NamedView.Tv_Let (r, attrs, b, t1, t2) ->
                  "Tv_Let"
              | FStar_Tactics_NamedView.Tv_Match (t1, uu___3, branches) ->
                  "Tv_Match"
              | FStar_Tactics_NamedView.Tv_AscribedT
                  (uu___3, uu___4, uu___5, uu___6) -> "Tv_AscribedT"
              | FStar_Tactics_NamedView.Tv_AscribedC
                  (uu___3, uu___4, uu___5, uu___6) -> "Tv_AscribedC"
              | FStar_Tactics_NamedView.Tv_Unknown -> "Tv_Unknown"
              | FStar_Tactics_NamedView.Tv_Unsupp -> "Tv_Unsupp"))
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
                (let uu___1 =
                   let uu___2 =
                     let uu___3 =
                       FStarC_Tactics_V2_Builtins.term_to_string tm in
                     FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "FStar.Tactics.PatternMatching.fst"
                                (Prims.of_int (228)) (Prims.of_int (37))
                                (Prims.of_int (228)) (Prims.of_int (54)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Prims.fst"
                                (Prims.of_int (611)) (Prims.of_int (19))
                                (Prims.of_int (611)) (Prims.of_int (31)))))
                       (Obj.magic uu___3)
                       (fun uu___4 ->
                          FStar_Tactics_Effect.lift_div_tac
                            (fun uu___5 -> Prims.strcat ", got " uu___4)) in
                   FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "FStar.Tactics.PatternMatching.fst"
                              (Prims.of_int (228)) (Prims.of_int (26))
                              (Prims.of_int (228)) (Prims.of_int (54)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Prims.fst"
                              (Prims.of_int (611)) (Prims.of_int (19))
                              (Prims.of_int (611)) (Prims.of_int (31)))))
                     (Obj.magic uu___2)
                     (fun uu___3 ->
                        FStar_Tactics_Effect.lift_div_tac
                          (fun uu___4 ->
                             Prims.strcat (desc_of_pattern pat) uu___3)) in
                 FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range
                            "FStar.Tactics.PatternMatching.fst"
                            (Prims.of_int (228)) (Prims.of_int (4))
                            (Prims.of_int (228)) (Prims.of_int (54)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Prims.fst"
                            (Prims.of_int (611)) (Prims.of_int (19))
                            (Prims.of_int (611)) (Prims.of_int (31)))))
                   (Obj.magic uu___1)
                   (fun uu___2 ->
                      FStar_Tactics_Effect.lift_div_tac
                        (fun uu___3 ->
                           Prims.strcat
                             "Match failure (sort mismatch): expecting "
                             uu___2))))
       | NonLinearMismatch (nm, t1, t2) ->
           Obj.magic
             (Obj.repr
                (let uu___1 =
                   let uu___2 =
                     let uu___3 =
                       let uu___4 =
                         FStarC_Tactics_V2_Builtins.term_to_string t1 in
                       FStar_Tactics_Effect.tac_bind
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "FStar.Tactics.PatternMatching.fst"
                                  (Prims.of_int (231)) (Prims.of_int (30))
                                  (Prims.of_int (231)) (Prims.of_int (49)))))
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "FStar.Tactics.PatternMatching.fst"
                                  (Prims.of_int (231)) (Prims.of_int (30))
                                  (Prims.of_int (232)) (Prims.of_int (33)))))
                         (Obj.magic uu___4)
                         (fun uu___5 ->
                            (fun uu___5 ->
                               let uu___6 =
                                 let uu___7 =
                                   FStarC_Tactics_V2_Builtins.term_to_string
                                     t2 in
                                 FStar_Tactics_Effect.tac_bind
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "FStar.Tactics.PatternMatching.fst"
                                            (Prims.of_int (232))
                                            (Prims.of_int (14))
                                            (Prims.of_int (232))
                                            (Prims.of_int (33)))))
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range "Prims.fst"
                                            (Prims.of_int (611))
                                            (Prims.of_int (19))
                                            (Prims.of_int (611))
                                            (Prims.of_int (31)))))
                                   (Obj.magic uu___7)
                                   (fun uu___8 ->
                                      FStar_Tactics_Effect.lift_div_tac
                                        (fun uu___9 ->
                                           Prims.strcat " and " uu___8)) in
                               Obj.magic
                                 (FStar_Tactics_Effect.tac_bind
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "FStar.Tactics.PatternMatching.fst"
                                             (Prims.of_int (232))
                                             (Prims.of_int (4))
                                             (Prims.of_int (232))
                                             (Prims.of_int (33)))))
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range "Prims.fst"
                                             (Prims.of_int (611))
                                             (Prims.of_int (19))
                                             (Prims.of_int (611))
                                             (Prims.of_int (31)))))
                                    (Obj.magic uu___6)
                                    (fun uu___7 ->
                                       FStar_Tactics_Effect.lift_div_tac
                                         (fun uu___8 ->
                                            Prims.strcat uu___5 uu___7))))
                              uu___5) in
                     FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "FStar.Tactics.PatternMatching.fst"
                                (Prims.of_int (231)) (Prims.of_int (30))
                                (Prims.of_int (232)) (Prims.of_int (33)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "Prims.fst"
                                (Prims.of_int (611)) (Prims.of_int (19))
                                (Prims.of_int (611)) (Prims.of_int (31)))))
                       (Obj.magic uu___3)
                       (fun uu___4 ->
                          FStar_Tactics_Effect.lift_div_tac
                            (fun uu___5 ->
                               Prims.strcat " needs to match both " uu___4)) in
                   FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "FStar.Tactics.PatternMatching.fst"
                              (Prims.of_int (231)) (Prims.of_int (4))
                              (Prims.of_int (232)) (Prims.of_int (33)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Prims.fst"
                              (Prims.of_int (611)) (Prims.of_int (19))
                              (Prims.of_int (611)) (Prims.of_int (31)))))
                     (Obj.magic uu___2)
                     (fun uu___3 ->
                        FStar_Tactics_Effect.lift_div_tac
                          (fun uu___4 -> Prims.strcat nm uu___3)) in
                 FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range
                            "FStar.Tactics.PatternMatching.fst"
                            (Prims.of_int (230)) (Prims.of_int (54))
                            (Prims.of_int (232)) (Prims.of_int (33)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Prims.fst"
                            (Prims.of_int (611)) (Prims.of_int (19))
                            (Prims.of_int (611)) (Prims.of_int (31)))))
                   (Obj.magic uu___1)
                   (fun uu___2 ->
                      FStar_Tactics_Effect.lift_div_tac
                        (fun uu___3 ->
                           Prims.strcat
                             "Match failure (nonlinear mismatch): variable "
                             uu___2))))
       | UnsupportedTermInPattern tm ->
           Obj.magic
             (Obj.repr
                (let uu___1 =
                   let uu___2 = FStarC_Tactics_V2_Builtins.term_to_string tm in
                   FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "FStar.Tactics.PatternMatching.fst"
                              (Prims.of_int (235)) (Prims.of_int (4))
                              (Prims.of_int (235)) (Prims.of_int (21)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "FStar.Tactics.PatternMatching.fst"
                              (Prims.of_int (235)) (Prims.of_int (4))
                              (Prims.of_int (235)) (Prims.of_int (49)))))
                     (Obj.magic uu___2)
                     (fun uu___3 ->
                        (fun uu___3 ->
                           let uu___4 =
                             let uu___5 =
                               let uu___6 = term_head tm in
                               FStar_Tactics_Effect.tac_bind
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "FStar.Tactics.PatternMatching.fst"
                                          (Prims.of_int (235))
                                          (Prims.of_int (31))
                                          (Prims.of_int (235))
                                          (Prims.of_int (43)))))
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range "Prims.fst"
                                          (Prims.of_int (611))
                                          (Prims.of_int (19))
                                          (Prims.of_int (611))
                                          (Prims.of_int (31)))))
                                 (Obj.magic uu___6)
                                 (fun uu___7 ->
                                    FStar_Tactics_Effect.lift_div_tac
                                      (fun uu___8 -> Prims.strcat uu___7 ")")) in
                             FStar_Tactics_Effect.tac_bind
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "FStar.Tactics.PatternMatching.fst"
                                        (Prims.of_int (235))
                                        (Prims.of_int (31))
                                        (Prims.of_int (235))
                                        (Prims.of_int (49)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range "Prims.fst"
                                        (Prims.of_int (611))
                                        (Prims.of_int (19))
                                        (Prims.of_int (611))
                                        (Prims.of_int (31)))))
                               (Obj.magic uu___5)
                               (fun uu___6 ->
                                  FStar_Tactics_Effect.lift_div_tac
                                    (fun uu___7 -> Prims.strcat " (" uu___6)) in
                           Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "FStar.Tactics.PatternMatching.fst"
                                         (Prims.of_int (235))
                                         (Prims.of_int (24))
                                         (Prims.of_int (235))
                                         (Prims.of_int (49)))))
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range "Prims.fst"
                                         (Prims.of_int (611))
                                         (Prims.of_int (19))
                                         (Prims.of_int (611))
                                         (Prims.of_int (31)))))
                                (Obj.magic uu___4)
                                (fun uu___5 ->
                                   FStar_Tactics_Effect.lift_div_tac
                                     (fun uu___6 ->
                                        Prims.strcat uu___3 uu___5)))) uu___3) in
                 FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range
                            "FStar.Tactics.PatternMatching.fst"
                            (Prims.of_int (235)) (Prims.of_int (4))
                            (Prims.of_int (235)) (Prims.of_int (49)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Prims.fst"
                            (Prims.of_int (611)) (Prims.of_int (19))
                            (Prims.of_int (611)) (Prims.of_int (31)))))
                   (Obj.magic uu___1)
                   (fun uu___2 ->
                      FStar_Tactics_Effect.lift_div_tac
                        (fun uu___3 ->
                           Prims.strcat
                             "Match failure (unsupported term in pattern): "
                             uu___2))))
       | IncorrectTypeInAbsPatBinder typ ->
           Obj.magic
             (Obj.repr
                (let uu___1 =
                   let uu___2 = FStarC_Tactics_V2_Builtins.term_to_string typ in
                   FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "FStar.Tactics.PatternMatching.fst"
                              (Prims.of_int (238)) (Prims.of_int (4))
                              (Prims.of_int (238)) (Prims.of_int (22)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Prims.fst"
                              (Prims.of_int (611)) (Prims.of_int (19))
                              (Prims.of_int (611)) (Prims.of_int (31)))))
                     (Obj.magic uu___2)
                     (fun uu___3 ->
                        FStar_Tactics_Effect.lift_div_tac
                          (fun uu___4 ->
                             Prims.strcat uu___3
                               " (use one of ``var``, ``hyp \226\128\166``, or ``goal \226\128\166``)")) in
                 FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range
                            "FStar.Tactics.PatternMatching.fst"
                            (Prims.of_int (238)) (Prims.of_int (4))
                            (Prims.of_int (238)) (Prims.of_int (74)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Prims.fst"
                            (Prims.of_int (611)) (Prims.of_int (19))
                            (Prims.of_int (611)) (Prims.of_int (31)))))
                   (Obj.magic uu___1)
                   (fun uu___2 ->
                      FStar_Tactics_Effect.lift_div_tac
                        (fun uu___3 ->
                           Prims.strcat
                             "Incorrect type in pattern-matching binder: "
                             uu___2))))) uu___
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
                    (let uu___ = string_of_match_exception ex in
                     FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "FStar.Tactics.PatternMatching.fst"
                                (Prims.of_int (269)) (Prims.of_int (31))
                                (Prims.of_int (269)) (Prims.of_int (61)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "FStar.Tactics.PatternMatching.fst"
                                (Prims.of_int (269)) (Prims.of_int (18))
                                (Prims.of_int (269)) (Prims.of_int (61)))))
                       (Obj.magic uu___)
                       (fun uu___1 -> FStar_Tactics_V1_Derived.fail uu___1))))
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
                    (let uu___ = string_of_match_exception ex in
                     FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "FStar.Tactics.PatternMatching.fst"
                                (Prims.of_int (274)) (Prims.of_int (31))
                                (Prims.of_int (274)) (Prims.of_int (61)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "FStar.Tactics.PatternMatching.fst"
                                (Prims.of_int (274)) (Prims.of_int (18))
                                (Prims.of_int (274)) (Prims.of_int (61)))))
                       (Obj.magic uu___)
                       (fun uu___1 -> FStar_Tactics_V1_Derived.fail uu___1))))
        uu___1 uu___
type bindings = (varname * FStar_Tactics_NamedView.term) Prims.list
let (string_of_bindings :
  bindings -> (Prims.string, unit) FStar_Tactics_Effect.tac_repr) =
  fun bindings1 ->
    let uu___ =
      FStar_Tactics_Util.map
        (fun uu___1 ->
           match uu___1 with
           | (nm, tm) ->
               let uu___2 =
                 let uu___3 =
                   let uu___4 = FStarC_Tactics_V2_Builtins.term_to_string tm in
                   FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "FStar.Tactics.PatternMatching.fst"
                              (Prims.of_int (286)) (Prims.of_int (47))
                              (Prims.of_int (286)) (Prims.of_int (64)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Prims.fst"
                              (Prims.of_int (611)) (Prims.of_int (19))
                              (Prims.of_int (611)) (Prims.of_int (31)))))
                     (Obj.magic uu___4)
                     (fun uu___5 ->
                        FStar_Tactics_Effect.lift_div_tac
                          (fun uu___6 -> Prims.strcat ": " uu___5)) in
                 FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range
                            "FStar.Tactics.PatternMatching.fst"
                            (Prims.of_int (286)) (Prims.of_int (40))
                            (Prims.of_int (286)) (Prims.of_int (64)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Prims.fst"
                            (Prims.of_int (611)) (Prims.of_int (19))
                            (Prims.of_int (611)) (Prims.of_int (31)))))
                   (Obj.magic uu___3)
                   (fun uu___4 ->
                      FStar_Tactics_Effect.lift_div_tac
                        (fun uu___5 -> Prims.strcat nm uu___4)) in
               FStar_Tactics_Effect.tac_bind
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range
                          "FStar.Tactics.PatternMatching.fst"
                          (Prims.of_int (286)) (Prims.of_int (35))
                          (Prims.of_int (286)) (Prims.of_int (64)))))
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "Prims.fst" (Prims.of_int (611))
                          (Prims.of_int (19)) (Prims.of_int (611))
                          (Prims.of_int (31))))) (Obj.magic uu___2)
                 (fun uu___3 ->
                    FStar_Tactics_Effect.lift_div_tac
                      (fun uu___4 -> Prims.strcat ">> " uu___3))) bindings1 in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.PatternMatching.fst"
               (Prims.of_int (286)) (Prims.of_int (4)) (Prims.of_int (287))
               (Prims.of_int (27)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.PatternMatching.fst"
               (Prims.of_int (285)) (Prims.of_int (2)) (Prims.of_int (287))
               (Prims.of_int (27))))) (Obj.magic uu___)
      (fun uu___1 ->
         FStar_Tactics_Effect.lift_div_tac
           (fun uu___2 -> FStar_String.concat "\n" uu___1))
let rec (interp_pattern_aux :
  pattern ->
    bindings ->
      FStar_Tactics_NamedView.term ->
        (bindings match_res, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun pat ->
    fun cur_bindings ->
      fun tm ->
        let uu___ =
          Obj.magic
            (FStar_Tactics_Effect.lift_div_tac
               (fun uu___1 ->
                  fun v ->
                    fun cur_bindings1 ->
                      fun tm1 ->
                        match FStar_List_Tot_Base.assoc v cur_bindings1 with
                        | FStar_Pervasives_Native.Some tm' ->
                            if FStar_Reflection_TermEq_Simple.term_eq tm1 tm'
                            then return cur_bindings1
                            else raise (NonLinearMismatch (v, tm1, tm'))
                        | FStar_Pervasives_Native.None ->
                            return ((v, tm1) :: cur_bindings1))) in
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.PatternMatching.fst"
                   (Prims.of_int (295)) (Prims.of_int (4))
                   (Prims.of_int (298)) (Prims.of_int (46)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.PatternMatching.fst"
                   (Prims.of_int (298)) (Prims.of_int (49))
                   (Prims.of_int (321)) (Prims.of_int (62)))))
          (Obj.magic uu___)
          (fun uu___1 ->
             (fun interp_var ->
                let uu___1 =
                  Obj.magic
                    (FStar_Tactics_Effect.lift_div_tac
                       (fun uu___2 ->
                          fun qn1 ->
                            fun cur_bindings1 ->
                              fun tm1 ->
                                let uu___3 =
                                  FStar_Tactics_NamedView.inspect tm1 in
                                FStar_Tactics_Effect.tac_bind
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "FStar.Tactics.PatternMatching.fst"
                                           (Prims.of_int (300))
                                           (Prims.of_int (10))
                                           (Prims.of_int (300))
                                           (Prims.of_int (20)))))
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "FStar.Tactics.PatternMatching.fst"
                                           (Prims.of_int (300))
                                           (Prims.of_int (4))
                                           (Prims.of_int (305))
                                           (Prims.of_int (43)))))
                                  (Obj.magic uu___3)
                                  (fun uu___4 ->
                                     FStar_Tactics_Effect.lift_div_tac
                                       (fun uu___5 ->
                                          match uu___4 with
                                          | FStar_Tactics_NamedView.Tv_UInst
                                              (fv, uu___6) ->
                                              if
                                                (FStar_Reflection_V2_Derived.fv_to_string
                                                   fv)
                                                  = qn1
                                              then return cur_bindings1
                                              else
                                                raise
                                                  (NameMismatch
                                                     (qn1,
                                                       (FStar_Reflection_V2_Derived.fv_to_string
                                                          fv)))
                                          | FStar_Tactics_NamedView.Tv_FVar
                                              fv ->
                                              if
                                                (FStar_Reflection_V2_Derived.fv_to_string
                                                   fv)
                                                  = qn1
                                              then return cur_bindings1
                                              else
                                                raise
                                                  (NameMismatch
                                                     (qn1,
                                                       (FStar_Reflection_V2_Derived.fv_to_string
                                                          fv)))
                                          | uu___6 ->
                                              raise
                                                (SimpleMismatch (pat, tm1)))))) in
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "FStar.Tactics.PatternMatching.fst"
                              (Prims.of_int (300)) (Prims.of_int (4))
                              (Prims.of_int (305)) (Prims.of_int (43)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "FStar.Tactics.PatternMatching.fst"
                              (Prims.of_int (305)) (Prims.of_int (46))
                              (Prims.of_int (321)) (Prims.of_int (62)))))
                     (Obj.magic uu___1)
                     (fun uu___2 ->
                        (fun interp_qn ->
                           let uu___2 =
                             Obj.magic
                               (FStar_Tactics_Effect.lift_div_tac
                                  (fun uu___3 ->
                                     fun cur_bindings1 ->
                                       fun tm1 ->
                                         let uu___4 =
                                           FStar_Tactics_NamedView.inspect
                                             tm1 in
                                         FStar_Tactics_Effect.tac_bind
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "FStar.Tactics.PatternMatching.fst"
                                                    (Prims.of_int (307))
                                                    (Prims.of_int (10))
                                                    (Prims.of_int (307))
                                                    (Prims.of_int (20)))))
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "FStar.Tactics.PatternMatching.fst"
                                                    (Prims.of_int (307))
                                                    (Prims.of_int (4))
                                                    (Prims.of_int (309))
                                                    (Prims.of_int (43)))))
                                           (Obj.magic uu___4)
                                           (fun uu___5 ->
                                              FStar_Tactics_Effect.lift_div_tac
                                                (fun uu___6 ->
                                                   match uu___5 with
                                                   | FStar_Tactics_NamedView.Tv_Type
                                                       uu___7 ->
                                                       return cur_bindings1
                                                   | uu___7 ->
                                                       raise
                                                         (SimpleMismatch
                                                            (pat, tm1)))))) in
                           Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "FStar.Tactics.PatternMatching.fst"
                                         (Prims.of_int (307))
                                         (Prims.of_int (4))
                                         (Prims.of_int (309))
                                         (Prims.of_int (43)))))
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "FStar.Tactics.PatternMatching.fst"
                                         (Prims.of_int (309))
                                         (Prims.of_int (46))
                                         (Prims.of_int (321))
                                         (Prims.of_int (62)))))
                                (Obj.magic uu___2)
                                (fun uu___3 ->
                                   (fun interp_type ->
                                      let uu___3 =
                                        Obj.magic
                                          (FStar_Tactics_Effect.lift_div_tac
                                             (fun uu___4 ->
                                                fun p_hd ->
                                                  fun p_arg ->
                                                    fun cur_bindings1 ->
                                                      fun tm1 ->
                                                        let uu___5 =
                                                          FStar_Tactics_NamedView.inspect
                                                            tm1 in
                                                        FStar_Tactics_Effect.tac_bind
                                                          (FStar_Sealed.seal
                                                             (Obj.magic
                                                                (FStar_Range.mk_range
                                                                   "FStar.Tactics.PatternMatching.fst"
                                                                   (Prims.of_int (311))
                                                                   (Prims.of_int (10))
                                                                   (Prims.of_int (311))
                                                                   (Prims.of_int (20)))))
                                                          (FStar_Sealed.seal
                                                             (Obj.magic
                                                                (FStar_Range.mk_range
                                                                   "FStar.Tactics.PatternMatching.fst"
                                                                   (Prims.of_int (311))
                                                                   (Prims.of_int (4))
                                                                   (Prims.of_int (316))
                                                                   (Prims.of_int (43)))))
                                                          (Obj.magic uu___5)
                                                          (fun uu___6 ->
                                                             (fun uu___6 ->
                                                                match uu___6
                                                                with
                                                                | FStar_Tactics_NamedView.Tv_App
                                                                    (hd,
                                                                    (arg,
                                                                    uu___7))
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (let uu___8
                                                                    =
                                                                    interp_pattern_aux
                                                                    p_hd
                                                                    cur_bindings1
                                                                    hd in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (313))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (313))
                                                                    (Prims.of_int (60)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (313))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (315))
                                                                    (Prims.of_int (21)))))
                                                                    (Obj.magic
                                                                    uu___8)
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun
                                                                    uu___9 ->
                                                                    Obj.magic
                                                                    (op_let_Question
                                                                    uu___9
                                                                    (fun
                                                                    with_hd
                                                                    ->
                                                                    let uu___10
                                                                    =
                                                                    interp_pattern_aux
                                                                    p_arg
                                                                    with_hd
                                                                    arg in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (314))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (314))
                                                                    (Prims.of_int (58)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (314))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (315))
                                                                    (Prims.of_int (21)))))
                                                                    (Obj.magic
                                                                    uu___10)
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    Obj.magic
                                                                    (op_let_Question
                                                                    uu___11
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    (fun
                                                                    with_arg
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    return
                                                                    with_arg)))
                                                                    uu___12)))
                                                                    uu___11))))
                                                                    uu___9)))
                                                                | uu___7 ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    raise
                                                                    (SimpleMismatch
                                                                    (pat,
                                                                    tm1))))))
                                                               uu___6))) in
                                      Obj.magic
                                        (FStar_Tactics_Effect.tac_bind
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "FStar.Tactics.PatternMatching.fst"
                                                    (Prims.of_int (311))
                                                    (Prims.of_int (4))
                                                    (Prims.of_int (316))
                                                    (Prims.of_int (43)))))
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "FStar.Tactics.PatternMatching.fst"
                                                    (Prims.of_int (317))
                                                    (Prims.of_int (4))
                                                    (Prims.of_int (321))
                                                    (Prims.of_int (62)))))
                                           (Obj.magic uu___3)
                                           (fun uu___4 ->
                                              (fun interp_app ->
                                                 match pat with
                                                 | PVar var ->
                                                     Obj.magic
                                                       (Obj.repr
                                                          (FStar_Tactics_Effect.lift_div_tac
                                                             (fun uu___4 ->
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
                                                             cur_bindings tm)))
                                                uu___4))) uu___3))) uu___2)))
               uu___1)
let (interp_pattern :
  pattern ->
    FStar_Tactics_NamedView.term ->
      (bindings match_res, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun pat ->
    fun tm ->
      let uu___ = interp_pattern_aux pat [] tm in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.PatternMatching.fst"
                 (Prims.of_int (327)) (Prims.of_int (24))
                 (Prims.of_int (327)) (Prims.of_int (52)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.PatternMatching.fst"
                 (Prims.of_int (327)) (Prims.of_int (4)) (Prims.of_int (328))
                 (Prims.of_int (43))))) (Obj.magic uu___)
        (fun uu___1 ->
           (fun uu___1 ->
              Obj.magic
                (op_let_Question uu___1
                   (fun uu___2 ->
                      (fun rev_bindings ->
                         Obj.magic
                           (FStar_Tactics_Effect.lift_div_tac
                              (fun uu___2 ->
                                 return
                                   (FStar_List_Tot_Base.rev rev_bindings))))
                        uu___2))) uu___1)
let (match_term :
  pattern ->
    FStar_Tactics_NamedView.term ->
      (bindings, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun pat ->
    fun tm ->
      let uu___ =
        let uu___1 = FStar_Tactics_V2_Derived.norm_term [] tm in
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.PatternMatching.fst"
                   (Prims.of_int (334)) (Prims.of_int (29))
                   (Prims.of_int (334)) (Prims.of_int (46)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.PatternMatching.fst"
                   (Prims.of_int (334)) (Prims.of_int (10))
                   (Prims.of_int (334)) (Prims.of_int (46)))))
          (Obj.magic uu___1)
          (fun uu___2 ->
             (fun uu___2 -> Obj.magic (interp_pattern pat uu___2)) uu___2) in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.PatternMatching.fst"
                 (Prims.of_int (334)) (Prims.of_int (10))
                 (Prims.of_int (334)) (Prims.of_int (46)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.PatternMatching.fst"
                 (Prims.of_int (334)) (Prims.of_int (4)) (Prims.of_int (336))
                 (Prims.of_int (63))))) (Obj.magic uu___)
        (fun uu___1 ->
           (fun uu___1 ->
              match uu___1 with
              | Success bb ->
                  Obj.magic
                    (Obj.repr
                       (FStar_Tactics_Effect.lift_div_tac (fun uu___2 -> bb)))
              | Failure ex ->
                  Obj.magic
                    (Obj.repr
                       (let uu___2 = string_of_match_exception ex in
                        FStar_Tactics_Effect.tac_bind
                          (FStar_Sealed.seal
                             (Obj.magic
                                (FStar_Range.mk_range
                                   "FStar.Tactics.PatternMatching.fst"
                                   (Prims.of_int (336)) (Prims.of_int (33))
                                   (Prims.of_int (336)) (Prims.of_int (63)))))
                          (FStar_Sealed.seal
                             (Obj.magic
                                (FStar_Range.mk_range
                                   "FStar.Tactics.PatternMatching.fst"
                                   (Prims.of_int (336)) (Prims.of_int (20))
                                   (Prims.of_int (336)) (Prims.of_int (63)))))
                          (Obj.magic uu___2)
                          (fun uu___3 -> FStar_Tactics_V1_Derived.fail uu___3))))
             uu___1)
let debug : 'uuuuu . 'uuuuu -> (unit, unit) FStar_Tactics_Effect.tac_repr =
  fun uu___ ->
    (fun msg ->
       Obj.magic (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> ()))) uu___
type absvar = FStar_Tactics_NamedView.binding
type hypothesis = FStar_Tactics_NamedView.binding
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
  ms_vars: (varname * FStar_Tactics_NamedView.term) Prims.list ;
  ms_hyps: (varname * hypothesis) Prims.list }
let (__proj__Mkmatching_solution__item__ms_vars :
  matching_solution -> (varname * FStar_Tactics_NamedView.term) Prims.list) =
  fun projectee -> match projectee with | { ms_vars; ms_hyps;_} -> ms_vars
let (__proj__Mkmatching_solution__item__ms_hyps :
  matching_solution -> (varname * hypothesis) Prims.list) =
  fun projectee -> match projectee with | { ms_vars; ms_hyps;_} -> ms_hyps
let (string_of_matching_solution :
  matching_solution -> (Prims.string, unit) FStar_Tactics_Effect.tac_repr) =
  fun ms ->
    let uu___ =
      let uu___1 =
        FStar_Tactics_Util.map
          (fun uu___2 ->
             match uu___2 with
             | (varname1, tm) ->
                 let uu___3 =
                   let uu___4 = FStarC_Tactics_V2_Builtins.term_to_string tm in
                   FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "FStar.Tactics.PatternMatching.fst"
                              (Prims.of_int (385)) (Prims.of_int (25))
                              (Prims.of_int (385)) (Prims.of_int (44)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "Prims.fst"
                              (Prims.of_int (611)) (Prims.of_int (19))
                              (Prims.of_int (611)) (Prims.of_int (31)))))
                     (Obj.magic uu___4)
                     (fun uu___5 ->
                        FStar_Tactics_Effect.lift_div_tac
                          (fun uu___6 -> Prims.strcat ": " uu___5)) in
                 FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range
                            "FStar.Tactics.PatternMatching.fst"
                            (Prims.of_int (385)) (Prims.of_int (18))
                            (Prims.of_int (385)) (Prims.of_int (44)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Prims.fst"
                            (Prims.of_int (611)) (Prims.of_int (19))
                            (Prims.of_int (611)) (Prims.of_int (31)))))
                   (Obj.magic uu___3)
                   (fun uu___4 ->
                      FStar_Tactics_Effect.lift_div_tac
                        (fun uu___5 -> Prims.strcat varname1 uu___4)))
          ms.ms_vars in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.PatternMatching.fst"
                 (Prims.of_int (384)) (Prims.of_int (6)) (Prims.of_int (385))
                 (Prims.of_int (57)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.PatternMatching.fst"
                 (Prims.of_int (383)) (Prims.of_int (4)) (Prims.of_int (385))
                 (Prims.of_int (57))))) (Obj.magic uu___1)
        (fun uu___2 ->
           FStar_Tactics_Effect.lift_div_tac
             (fun uu___3 -> FStar_String.concat "\n            " uu___2)) in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.PatternMatching.fst"
               (Prims.of_int (383)) (Prims.of_int (4)) (Prims.of_int (385))
               (Prims.of_int (57)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.PatternMatching.fst"
               (Prims.of_int (385)) (Prims.of_int (60)) (Prims.of_int (391))
               (Prims.of_int (26))))) (Obj.magic uu___)
      (fun uu___1 ->
         (fun vars ->
            let uu___1 =
              let uu___2 =
                FStar_Tactics_Util.map
                  (fun uu___3 ->
                     match uu___3 with
                     | (nm, binding) ->
                         let uu___4 =
                           let uu___5 =
                             FStar_Tactics_V2_Derived.binding_to_string
                               binding in
                           FStar_Tactics_Effect.tac_bind
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "FStar.Tactics.PatternMatching.fst"
                                      (Prims.of_int (389))
                                      (Prims.of_int (20))
                                      (Prims.of_int (389))
                                      (Prims.of_int (47)))))
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range "Prims.fst"
                                      (Prims.of_int (611))
                                      (Prims.of_int (19))
                                      (Prims.of_int (611))
                                      (Prims.of_int (31)))))
                             (Obj.magic uu___5)
                             (fun uu___6 ->
                                FStar_Tactics_Effect.lift_div_tac
                                  (fun uu___7 -> Prims.strcat ": " uu___6)) in
                         FStar_Tactics_Effect.tac_bind
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "FStar.Tactics.PatternMatching.fst"
                                    (Prims.of_int (389)) (Prims.of_int (13))
                                    (Prims.of_int (389)) (Prims.of_int (47)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range "Prims.fst"
                                    (Prims.of_int (611)) (Prims.of_int (19))
                                    (Prims.of_int (611)) (Prims.of_int (31)))))
                           (Obj.magic uu___4)
                           (fun uu___5 ->
                              FStar_Tactics_Effect.lift_div_tac
                                (fun uu___6 -> Prims.strcat nm uu___5)))
                  ms.ms_hyps in
              FStar_Tactics_Effect.tac_bind
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range
                         "FStar.Tactics.PatternMatching.fst"
                         (Prims.of_int (388)) (Prims.of_int (6))
                         (Prims.of_int (389)) (Prims.of_int (60)))))
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range
                         "FStar.Tactics.PatternMatching.fst"
                         (Prims.of_int (387)) (Prims.of_int (4))
                         (Prims.of_int (389)) (Prims.of_int (60)))))
                (Obj.magic uu___2)
                (fun uu___3 ->
                   FStar_Tactics_Effect.lift_div_tac
                     (fun uu___4 -> FStar_String.concat "\n        " uu___3)) in
            Obj.magic
              (FStar_Tactics_Effect.tac_bind
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range
                          "FStar.Tactics.PatternMatching.fst"
                          (Prims.of_int (387)) (Prims.of_int (4))
                          (Prims.of_int (389)) (Prims.of_int (60)))))
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "Prims.fst" (Prims.of_int (611))
                          (Prims.of_int (19)) (Prims.of_int (611))
                          (Prims.of_int (31))))) (Obj.magic uu___1)
                 (fun hyps ->
                    FStar_Tactics_Effect.lift_div_tac
                      (fun uu___2 ->
                         Prims.strcat "\n{ vars: "
                           (Prims.strcat vars
                              (Prims.strcat "\n"
                                 (Prims.strcat "  hyps: "
                                    (Prims.strcat hyps " }")))))))) uu___1)
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
                 (FStar_Tactics_V2_Derived.fail
                    (Prims.strcat "Not found: " key))
           | FStar_Pervasives_Native.Some x ->
               Obj.magic (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> x)))
        uu___1 uu___
let ms_locate_hyp :
  'a .
    matching_solution ->
      varname -> (hypothesis, unit) FStar_Tactics_Effect.tac_repr
  = fun solution -> fun name -> assoc_varname_fail name solution.ms_hyps
let ms_locate_var :
  'a .
    matching_solution -> varname -> ('a, unit) FStar_Tactics_Effect.tac_repr
  =
  fun solution ->
    fun name ->
      let uu___ = assoc_varname_fail name solution.ms_vars in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.PatternMatching.fst"
                 (Prims.of_int (406)) (Prims.of_int (13))
                 (Prims.of_int (406)) (Prims.of_int (55)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.PatternMatching.fst"
                 (Prims.of_int (406)) (Prims.of_int (2)) (Prims.of_int (406))
                 (Prims.of_int (55))))) (Obj.magic uu___)
        (fun uu___1 ->
           (fun uu___1 ->
              Obj.magic (FStarC_Tactics_V2_Builtins.unquote uu___1)) uu___1)
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
                                (FStar_Tactics_V2_Derived.fail
                                   "No matching hypothesis"))
                       | h::hs ->
                           Obj.magic
                             (Obj.repr
                                (FStar_Tactics_V2_Derived.or_else
                                   (fun uu___ ->
                                      let uu___1 =
                                        interp_pattern_aux pat
                                          part_sol.ms_vars
                                          (FStar_Tactics_V2_Derived.type_of_binding
                                             h) in
                                      FStar_Tactics_Effect.tac_bind
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "FStar.Tactics.PatternMatching.fst"
                                                 (Prims.of_int (446))
                                                 (Prims.of_int (15))
                                                 (Prims.of_int (446))
                                                 (Prims.of_int (74)))))
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "FStar.Tactics.PatternMatching.fst"
                                                 (Prims.of_int (446))
                                                 (Prims.of_int (9))
                                                 (Prims.of_int (451))
                                                 (Prims.of_int (73)))))
                                        (Obj.magic uu___1)
                                        (fun uu___2 ->
                                           (fun uu___2 ->
                                              match uu___2 with
                                              | Failure ex ->
                                                  let uu___3 =
                                                    let uu___4 =
                                                      string_of_match_exception
                                                        ex in
                                                    FStar_Tactics_Effect.tac_bind
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "FStar.Tactics.PatternMatching.fst"
                                                               (Prims.of_int (448))
                                                               (Prims.of_int (43))
                                                               (Prims.of_int (448))
                                                               (Prims.of_int (73)))))
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "Prims.fst"
                                                               (Prims.of_int (611))
                                                               (Prims.of_int (19))
                                                               (Prims.of_int (611))
                                                               (Prims.of_int (31)))))
                                                      (Obj.magic uu___4)
                                                      (fun uu___5 ->
                                                         FStar_Tactics_Effect.lift_div_tac
                                                           (fun uu___6 ->
                                                              Prims.strcat
                                                                "Failed to match hyp: "
                                                                uu___5)) in
                                                  Obj.magic
                                                    (FStar_Tactics_Effect.tac_bind
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "FStar.Tactics.PatternMatching.fst"
                                                                (Prims.of_int (448))
                                                                (Prims.of_int (16))
                                                                (Prims.of_int (448))
                                                                (Prims.of_int (74)))))
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "FStar.Tactics.PatternMatching.fst"
                                                                (Prims.of_int (448))
                                                                (Prims.of_int (11))
                                                                (Prims.of_int (448))
                                                                (Prims.of_int (74)))))
                                                       (Obj.magic uu___3)
                                                       (fun uu___4 ->
                                                          FStar_Tactics_V2_Derived.fail
                                                            uu___4))
                                              | Success bindings1 ->
                                                  let uu___3 =
                                                    Obj.magic
                                                      (FStar_Tactics_Effect.lift_div_tac
                                                         (fun uu___4 ->
                                                            (name, h) ::
                                                            (part_sol.ms_hyps))) in
                                                  Obj.magic
                                                    (FStar_Tactics_Effect.tac_bind
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "FStar.Tactics.PatternMatching.fst"
                                                                (Prims.of_int (450))
                                                                (Prims.of_int (25))
                                                                (Prims.of_int (450))
                                                                (Prims.of_int (54)))))
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "FStar.Tactics.PatternMatching.fst"
                                                                (Prims.of_int (451))
                                                                (Prims.of_int (11))
                                                                (Prims.of_int (451))
                                                                (Prims.of_int (73)))))
                                                       (Obj.magic uu___3)
                                                       (fun uu___4 ->
                                                          (fun ms_hyps ->
                                                             Obj.magic
                                                               (body
                                                                  {
                                                                    ms_vars =
                                                                    bindings1;
                                                                    ms_hyps
                                                                  })) uu___4)))
                                             uu___2))
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
      hypothesis Prims.list ->
        FStar_Tactics_NamedView.term ->
          (matching_solution -> ('a, unit) FStar_Tactics_Effect.tac_repr) ->
            ('a, unit) FStar_Tactics_Effect.tac_repr
  =
  fun problem ->
    fun hypotheses ->
      fun goal ->
        fun body ->
          let uu___ =
            match problem.mp_goal with
            | FStar_Pervasives_Native.None ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.lift_div_tac
                        (fun uu___1 -> { ms_vars = []; ms_hyps = [] })))
            | FStar_Pervasives_Native.Some pat ->
                Obj.magic
                  (Obj.repr
                     (let uu___1 = interp_pattern pat goal in
                      FStar_Tactics_Effect.tac_bind
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "FStar.Tactics.PatternMatching.fst"
                                 (Prims.of_int (482)) (Prims.of_int (12))
                                 (Prims.of_int (482)) (Prims.of_int (35)))))
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "FStar.Tactics.PatternMatching.fst"
                                 (Prims.of_int (482)) (Prims.of_int (6))
                                 (Prims.of_int (484)) (Prims.of_int (64)))))
                        (Obj.magic uu___1)
                        (fun uu___2 ->
                           (fun uu___2 ->
                              match uu___2 with
                              | Failure ex ->
                                  Obj.magic
                                    (Obj.repr
                                       (let uu___3 =
                                          let uu___4 =
                                            string_of_match_exception ex in
                                          FStar_Tactics_Effect.tac_bind
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "FStar.Tactics.PatternMatching.fst"
                                                     (Prims.of_int (483))
                                                     (Prims.of_int (55))
                                                     (Prims.of_int (483))
                                                     (Prims.of_int (85)))))
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Prims.fst"
                                                     (Prims.of_int (611))
                                                     (Prims.of_int (19))
                                                     (Prims.of_int (611))
                                                     (Prims.of_int (31)))))
                                            (Obj.magic uu___4)
                                            (fun uu___5 ->
                                               FStar_Tactics_Effect.lift_div_tac
                                                 (fun uu___6 ->
                                                    Prims.strcat
                                                      "Failed to match goal: "
                                                      uu___5)) in
                                        FStar_Tactics_Effect.tac_bind
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "FStar.Tactics.PatternMatching.fst"
                                                   (Prims.of_int (483))
                                                   (Prims.of_int (27))
                                                   (Prims.of_int (483))
                                                   (Prims.of_int (86)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "FStar.Tactics.PatternMatching.fst"
                                                   (Prims.of_int (483))
                                                   (Prims.of_int (22))
                                                   (Prims.of_int (483))
                                                   (Prims.of_int (86)))))
                                          (Obj.magic uu___3)
                                          (fun uu___4 ->
                                             FStar_Tactics_V2_Derived.fail
                                               uu___4)))
                              | Success bindings1 ->
                                  Obj.magic
                                    (Obj.repr
                                       (FStar_Tactics_Effect.lift_div_tac
                                          (fun uu___3 ->
                                             {
                                               ms_vars = bindings1;
                                               ms_hyps = []
                                             })))) uu___2))) in
          FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "FStar.Tactics.PatternMatching.fst"
                     (Prims.of_int (479)) (Prims.of_int (4))
                     (Prims.of_int (484)) (Prims.of_int (64)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "FStar.Tactics.PatternMatching.fst"
                     (Prims.of_int (485)) (Prims.of_int (2))
                     (Prims.of_int (485)) (Prims.of_int (62)))))
            (Obj.magic uu___)
            (fun uu___1 ->
               (fun goal_ps ->
                  Obj.magic
                    (solve_mp_for_hyps problem.mp_hyps hypotheses body
                       goal_ps)) uu___1)
let (name_of_namedv :
  FStar_Tactics_NamedView.namedv ->
    (Prims.string, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun x ->
    FStarC_Tactics_Unseal.unseal
      (FStar_Tactics_NamedView.inspect_namedv x).FStarC_Reflection_V2_Data.ppname
let rec (pattern_of_term_ex :
  FStarC_Reflection_Types.term ->
    (pattern match_res, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun tm ->
    let uu___ = FStar_Tactics_NamedView.inspect tm in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.PatternMatching.fst"
               (Prims.of_int (508)) (Prims.of_int (8)) (Prims.of_int (508))
               (Prims.of_int (18)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.PatternMatching.fst"
               (Prims.of_int (508)) (Prims.of_int (2)) (Prims.of_int (521))
               (Prims.of_int (44))))) (Obj.magic uu___)
      (fun uu___1 ->
         (fun uu___1 ->
            match uu___1 with
            | FStar_Tactics_NamedView.Tv_Var bv ->
                Obj.magic
                  (Obj.repr
                     (let uu___2 =
                        let uu___3 = name_of_namedv bv in
                        FStar_Tactics_Effect.tac_bind
                          (FStar_Sealed.seal
                             (Obj.magic
                                (FStar_Range.mk_range
                                   "FStar.Tactics.PatternMatching.fst"
                                   (Prims.of_int (510)) (Prims.of_int (17))
                                   (Prims.of_int (510)) (Prims.of_int (36)))))
                          (FStar_Sealed.seal
                             (Obj.magic
                                (FStar_Range.mk_range
                                   "FStar.Tactics.PatternMatching.fst"
                                   (Prims.of_int (510)) (Prims.of_int (11))
                                   (Prims.of_int (510)) (Prims.of_int (37)))))
                          (Obj.magic uu___3)
                          (fun uu___4 ->
                             FStar_Tactics_Effect.lift_div_tac
                               (fun uu___5 -> PVar uu___4)) in
                      FStar_Tactics_Effect.tac_bind
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "FStar.Tactics.PatternMatching.fst"
                                 (Prims.of_int (510)) (Prims.of_int (11))
                                 (Prims.of_int (510)) (Prims.of_int (37)))))
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "FStar.Tactics.PatternMatching.fst"
                                 (Prims.of_int (510)) (Prims.of_int (4))
                                 (Prims.of_int (510)) (Prims.of_int (37)))))
                        (Obj.magic uu___2)
                        (fun uu___3 ->
                           FStar_Tactics_Effect.lift_div_tac
                             (fun uu___4 -> return uu___3))))
            | FStar_Tactics_NamedView.Tv_FVar fv ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.lift_div_tac
                        (fun uu___2 ->
                           return
                             (PQn
                                (FStar_Reflection_V2_Derived.fv_to_string fv)))))
            | FStar_Tactics_NamedView.Tv_UInst (fv, uu___2) ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.lift_div_tac
                        (fun uu___3 ->
                           return
                             (PQn
                                (FStar_Reflection_V2_Derived.fv_to_string fv)))))
            | FStar_Tactics_NamedView.Tv_Type uu___2 ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.lift_div_tac
                        (fun uu___3 -> return PType)))
            | FStar_Tactics_NamedView.Tv_App (f, (x, uu___2)) ->
                Obj.magic
                  (Obj.repr
                     (let uu___3 = pattern_of_term_ex f in
                      FStar_Tactics_Effect.tac_bind
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "FStar.Tactics.PatternMatching.fst"
                                 (Prims.of_int (518)) (Prims.of_int (17))
                                 (Prims.of_int (518)) (Prims.of_int (37)))))
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "FStar.Tactics.PatternMatching.fst"
                                 (Prims.of_int (518)) (Prims.of_int (5))
                                 (Prims.of_int (520)) (Prims.of_int (28)))))
                        (Obj.magic uu___3)
                        (fun uu___4 ->
                           (fun uu___4 ->
                              Obj.magic
                                (op_let_Question uu___4
                                   (fun fpat ->
                                      let uu___5 = pattern_of_term_ex x in
                                      FStar_Tactics_Effect.tac_bind
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "FStar.Tactics.PatternMatching.fst"
                                                 (Prims.of_int (519))
                                                 (Prims.of_int (17))
                                                 (Prims.of_int (519))
                                                 (Prims.of_int (37)))))
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "FStar.Tactics.PatternMatching.fst"
                                                 (Prims.of_int (519))
                                                 (Prims.of_int (5))
                                                 (Prims.of_int (520))
                                                 (Prims.of_int (28)))))
                                        (Obj.magic uu___5)
                                        (fun uu___6 ->
                                           (fun uu___6 ->
                                              Obj.magic
                                                (op_let_Question uu___6
                                                   (fun uu___7 ->
                                                      (fun xpat ->
                                                         Obj.magic
                                                           (FStar_Tactics_Effect.lift_div_tac
                                                              (fun uu___7 ->
                                                                 return
                                                                   (PApp
                                                                    (fpat,
                                                                    xpat)))))
                                                        uu___7))) uu___6))))
                             uu___4)))
            | uu___2 ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.lift_div_tac
                        (fun uu___3 -> raise (UnsupportedTermInPattern tm)))))
           uu___1)
let (beta_reduce :
  FStar_Tactics_NamedView.term ->
    (FStar_Tactics_NamedView.term, unit) FStar_Tactics_Effect.tac_repr)
  = fun tm -> FStar_Tactics_V2_Derived.norm_term [] tm
let (pattern_of_term :
  FStarC_Reflection_Types.term ->
    (pattern, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun tm ->
    let uu___ = pattern_of_term_ex tm in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.PatternMatching.fst"
               (Prims.of_int (531)) (Prims.of_int (10)) (Prims.of_int (531))
               (Prims.of_int (31)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.PatternMatching.fst"
               (Prims.of_int (531)) (Prims.of_int (4)) (Prims.of_int (533))
               (Prims.of_int (63))))) (Obj.magic uu___)
      (fun uu___1 ->
         (fun uu___1 ->
            match uu___1 with
            | Success bb ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.lift_div_tac (fun uu___2 -> bb)))
            | Failure ex ->
                Obj.magic
                  (Obj.repr
                     (let uu___2 = string_of_match_exception ex in
                      FStar_Tactics_Effect.tac_bind
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "FStar.Tactics.PatternMatching.fst"
                                 (Prims.of_int (533)) (Prims.of_int (33))
                                 (Prims.of_int (533)) (Prims.of_int (63)))))
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "FStar.Tactics.PatternMatching.fst"
                                 (Prims.of_int (533)) (Prims.of_int (20))
                                 (Prims.of_int (533)) (Prims.of_int (63)))))
                        (Obj.magic uu___2)
                        (fun uu___3 -> FStar_Tactics_V1_Derived.fail uu___3))))
           uu___1)
type 'a hyp = FStar_Tactics_NamedView.binding
type 'a pm_goal = unit
let (hyp_qn : Prims.string) = "FStar.Tactics.PatternMatching.hyp"
let (goal_qn : Prims.string) = "FStar.Tactics.PatternMatching.pm_goal"
type abspat_binder_kind =
  | ABKVar of FStarC_Reflection_Types.typ 
  | ABKHyp 
  | ABKGoal 
let (uu___is_ABKVar : abspat_binder_kind -> Prims.bool) =
  fun projectee -> match projectee with | ABKVar _0 -> true | uu___ -> false
let (__proj__ABKVar__item___0 :
  abspat_binder_kind -> FStarC_Reflection_Types.typ) =
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
  (abspat_argspec Prims.list * FStar_Tactics_NamedView.term)
let (type_of_named_binder :
  FStar_Tactics_NamedView.binder -> FStar_Tactics_NamedView.term) =
  fun nb -> nb.FStar_Tactics_NamedView.sort
let (classify_abspat_binder :
  FStar_Tactics_NamedView.binder ->
    ((abspat_binder_kind * FStar_Tactics_NamedView.term), unit)
      FStar_Tactics_Effect.tac_repr)
  =
  fun b ->
    let uu___ =
      Obj.magic (FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> "v")) in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.PatternMatching.fst"
               (Prims.of_int (588)) (Prims.of_int (16)) (Prims.of_int (588))
               (Prims.of_int (19)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.PatternMatching.fst"
               (Prims.of_int (588)) (Prims.of_int (22)) (Prims.of_int (600))
               (Prims.of_int (34))))) (Obj.magic uu___)
      (fun uu___1 ->
         (fun varname1 ->
            let uu___1 =
              Obj.magic
                (FStar_Tactics_Effect.lift_div_tac
                   (fun uu___2 -> PApp ((PQn hyp_qn), (PVar varname1)))) in
            Obj.magic
              (FStar_Tactics_Effect.tac_bind
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range
                          "FStar.Tactics.PatternMatching.fst"
                          (Prims.of_int (589)) (Prims.of_int (16))
                          (Prims.of_int (589)) (Prims.of_int (48)))))
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range
                          "FStar.Tactics.PatternMatching.fst"
                          (Prims.of_int (589)) (Prims.of_int (51))
                          (Prims.of_int (600)) (Prims.of_int (34)))))
                 (Obj.magic uu___1)
                 (fun uu___2 ->
                    (fun hyp_pat ->
                       let uu___2 =
                         Obj.magic
                           (FStar_Tactics_Effect.lift_div_tac
                              (fun uu___3 ->
                                 PApp ((PQn goal_qn), (PVar varname1)))) in
                       Obj.magic
                         (FStar_Tactics_Effect.tac_bind
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.PatternMatching.fst"
                                     (Prims.of_int (590)) (Prims.of_int (17))
                                     (Prims.of_int (590)) (Prims.of_int (50)))))
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.PatternMatching.fst"
                                     (Prims.of_int (590)) (Prims.of_int (53))
                                     (Prims.of_int (600)) (Prims.of_int (34)))))
                            (Obj.magic uu___2)
                            (fun uu___3 ->
                               (fun goal_pat ->
                                  let uu___3 =
                                    Obj.magic
                                      (FStar_Tactics_Effect.lift_div_tac
                                         (fun uu___4 ->
                                            type_of_named_binder b)) in
                                  Obj.magic
                                    (FStar_Tactics_Effect.tac_bind
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "FStar.Tactics.PatternMatching.fst"
                                                (Prims.of_int (592))
                                                (Prims.of_int (12))
                                                (Prims.of_int (592))
                                                (Prims.of_int (34)))))
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "FStar.Tactics.PatternMatching.fst"
                                                (Prims.of_int (593))
                                                (Prims.of_int (2))
                                                (Prims.of_int (600))
                                                (Prims.of_int (34)))))
                                       (Obj.magic uu___3)
                                       (fun uu___4 ->
                                          (fun typ ->
                                             let uu___4 =
                                               interp_pattern hyp_pat typ in
                                             Obj.magic
                                               (FStar_Tactics_Effect.tac_bind
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "FStar.Tactics.PatternMatching.fst"
                                                           (Prims.of_int (593))
                                                           (Prims.of_int (8))
                                                           (Prims.of_int (593))
                                                           (Prims.of_int (34)))))
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "FStar.Tactics.PatternMatching.fst"
                                                           (Prims.of_int (593))
                                                           (Prims.of_int (2))
                                                           (Prims.of_int (600))
                                                           (Prims.of_int (34)))))
                                                  (Obj.magic uu___4)
                                                  (fun uu___5 ->
                                                     (fun uu___5 ->
                                                        match uu___5 with
                                                        | Success
                                                            ((uu___6,
                                                              hyp_typ)::[])
                                                            ->
                                                            Obj.magic
                                                              (Obj.repr
                                                                 (FStar_Tactics_Effect.lift_div_tac
                                                                    (
                                                                    fun
                                                                    uu___7 ->
                                                                    (ABKHyp,
                                                                    hyp_typ))))
                                                        | Success uu___6 ->
                                                            Obj.magic
                                                              (Obj.repr
                                                                 (FStar_Tactics_V2_Derived.fail
                                                                    "classifiy_abspat_binder: impossible (1)"))
                                                        | Failure uu___6 ->
                                                            Obj.magic
                                                              (Obj.repr
                                                                 (let uu___7
                                                                    =
                                                                    interp_pattern
                                                                    goal_pat
                                                                    typ in
                                                                  FStar_Tactics_Effect.tac_bind
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (597))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (597))
                                                                    (Prims.of_int (37)))))
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (597))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (600))
                                                                    (Prims.of_int (34)))))
                                                                    (
                                                                    Obj.magic
                                                                    uu___7)
                                                                    (
                                                                    fun
                                                                    uu___8 ->
                                                                    match uu___8
                                                                    with
                                                                    | 
                                                                    Success
                                                                    ((uu___9,
                                                                    goal_typ)::[])
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (ABKGoal,
                                                                    goal_typ))
                                                                    | 
                                                                    Success
                                                                    uu___9 ->
                                                                    FStar_Tactics_V2_Derived.fail
                                                                    "classifiy_abspat_binder: impossible (2)"
                                                                    | 
                                                                    Failure
                                                                    uu___9 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    ((ABKVar
                                                                    typ),
                                                                    typ))))))
                                                       uu___5))) uu___4)))
                                 uu___3))) uu___2))) uu___1)
let rec (binders_and_body_of_abs :
  FStar_Tactics_NamedView.term ->
    ((FStar_Tactics_NamedView.binder Prims.list *
       FStar_Tactics_NamedView.term),
      unit) FStar_Tactics_Effect.tac_repr)
  =
  fun tm ->
    let uu___ = FStar_Tactics_NamedView.inspect tm in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.PatternMatching.fst"
               (Prims.of_int (604)) (Prims.of_int (8)) (Prims.of_int (604))
               (Prims.of_int (18)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.PatternMatching.fst"
               (Prims.of_int (604)) (Prims.of_int (2)) (Prims.of_int (608))
               (Prims.of_int (15))))) (Obj.magic uu___)
      (fun uu___1 ->
         (fun uu___1 ->
            match uu___1 with
            | FStar_Tactics_NamedView.Tv_Abs (binder, tm1) ->
                Obj.magic
                  (Obj.repr
                     (let uu___2 = binders_and_body_of_abs tm1 in
                      FStar_Tactics_Effect.tac_bind
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "FStar.Tactics.PatternMatching.fst"
                                 (Prims.of_int (606)) (Prims.of_int (24))
                                 (Prims.of_int (606)) (Prims.of_int (50)))))
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "FStar.Tactics.PatternMatching.fst"
                                 (Prims.of_int (605)) (Prims.of_int (23))
                                 (Prims.of_int (607)) (Prims.of_int (27)))))
                        (Obj.magic uu___2)
                        (fun uu___3 ->
                           FStar_Tactics_Effect.lift_div_tac
                             (fun uu___4 ->
                                match uu___3 with
                                | (binders, body) ->
                                    ((binder :: binders), body)))))
            | uu___2 ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.lift_div_tac
                        (fun uu___3 -> ([], tm))))) uu___1)
let (cleanup_abspat :
  FStar_Tactics_NamedView.term ->
    (FStar_Tactics_NamedView.term, unit) FStar_Tactics_Effect.tac_repr)
  = fun t -> FStar_Tactics_V2_Derived.norm_term [] t
let (name_of_named_binder :
  FStar_Tactics_NamedView.binder ->
    (Prims.string, unit) FStar_Tactics_Effect.tac_repr)
  = fun nb -> FStarC_Tactics_Unseal.unseal nb.FStar_Tactics_NamedView.ppname
let (matching_problem_of_abs :
  FStar_Tactics_NamedView.term ->
    ((matching_problem * abspat_continuation), unit)
      FStar_Tactics_Effect.tac_repr)
  =
  fun tm ->
    let uu___ =
      let uu___1 = cleanup_abspat tm in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.PatternMatching.fst"
                 (Prims.of_int (634)) (Prims.of_int (46))
                 (Prims.of_int (634)) (Prims.of_int (65)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.PatternMatching.fst"
                 (Prims.of_int (634)) (Prims.of_int (22))
                 (Prims.of_int (634)) (Prims.of_int (65)))))
        (Obj.magic uu___1)
        (fun uu___2 ->
           (fun uu___2 -> Obj.magic (binders_and_body_of_abs uu___2)) uu___2) in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.PatternMatching.fst"
               (Prims.of_int (634)) (Prims.of_int (22)) (Prims.of_int (634))
               (Prims.of_int (65)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.PatternMatching.fst"
               (Prims.of_int (632)) (Prims.of_int (52)) (Prims.of_int (673))
               (Prims.of_int (18))))) (Obj.magic uu___)
      (fun uu___1 ->
         (fun uu___1 ->
            match uu___1 with
            | (binders, body) ->
                let uu___2 =
                  let uu___3 =
                    let uu___4 =
                      let uu___5 =
                        FStar_Tactics_Util.map
                          (fun b -> name_of_named_binder b) binders in
                      FStar_Tactics_Effect.tac_bind
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "FStar.Tactics.PatternMatching.fst"
                                 (Prims.of_int (636)) (Prims.of_int (9))
                                 (Prims.of_int (636)) (Prims.of_int (70)))))
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "FStar.Tactics.PatternMatching.fst"
                                 (Prims.of_int (635)) (Prims.of_int (27))
                                 (Prims.of_int (636)) (Prims.of_int (71)))))
                        (Obj.magic uu___5)
                        (fun uu___6 ->
                           FStar_Tactics_Effect.lift_div_tac
                             (fun uu___7 -> FStar_String.concat ", " uu___6)) in
                    FStar_Tactics_Effect.tac_bind
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range
                               "FStar.Tactics.PatternMatching.fst"
                               (Prims.of_int (635)) (Prims.of_int (27))
                               (Prims.of_int (636)) (Prims.of_int (71)))))
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range "Prims.fst"
                               (Prims.of_int (611)) (Prims.of_int (19))
                               (Prims.of_int (611)) (Prims.of_int (31)))))
                      (Obj.magic uu___4)
                      (fun uu___5 ->
                         FStar_Tactics_Effect.lift_div_tac
                           (fun uu___6 -> Prims.strcat "Got binders: " uu___5)) in
                  FStar_Tactics_Effect.tac_bind
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range
                             "FStar.Tactics.PatternMatching.fst"
                             (Prims.of_int (635)) (Prims.of_int (8))
                             (Prims.of_int (636)) (Prims.of_int (72)))))
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range
                             "FStar.Tactics.PatternMatching.fst"
                             (Prims.of_int (635)) (Prims.of_int (2))
                             (Prims.of_int (636)) (Prims.of_int (72)))))
                    (Obj.magic uu___3)
                    (fun uu___4 ->
                       (fun uu___4 -> Obj.magic (debug uu___4)) uu___4) in
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "FStar.Tactics.PatternMatching.fst"
                              (Prims.of_int (635)) (Prims.of_int (2))
                              (Prims.of_int (636)) (Prims.of_int (72)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "FStar.Tactics.PatternMatching.fst"
                              (Prims.of_int (636)) (Prims.of_int (73))
                              (Prims.of_int (673)) (Prims.of_int (18)))))
                     (Obj.magic uu___2)
                     (fun uu___3 ->
                        (fun uu___3 ->
                           let uu___4 =
                             FStar_Tactics_Util.map
                               (fun binder ->
                                  let uu___5 = name_of_named_binder binder in
                                  FStar_Tactics_Effect.tac_bind
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "FStar.Tactics.PatternMatching.fst"
                                             (Prims.of_int (640))
                                             (Prims.of_int (22))
                                             (Prims.of_int (640))
                                             (Prims.of_int (49)))))
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "FStar.Tactics.PatternMatching.fst"
                                             (Prims.of_int (641))
                                             (Prims.of_int (8))
                                             (Prims.of_int (644))
                                             (Prims.of_int (43)))))
                                    (Obj.magic uu___5)
                                    (fun uu___6 ->
                                       (fun bv_name ->
                                          let uu___6 =
                                            let uu___7 =
                                              let uu___8 =
                                                let uu___9 =
                                                  let uu___10 =
                                                    FStarC_Tactics_V2_Builtins.term_to_string
                                                      (type_of_named_binder
                                                         binder) in
                                                  FStar_Tactics_Effect.tac_bind
                                                    (FStar_Sealed.seal
                                                       (Obj.magic
                                                          (FStar_Range.mk_range
                                                             "FStar.Tactics.PatternMatching.fst"
                                                             (Prims.of_int (642))
                                                             (Prims.of_int (15))
                                                             (Prims.of_int (642))
                                                             (Prims.of_int (59)))))
                                                    (FStar_Sealed.seal
                                                       (Obj.magic
                                                          (FStar_Range.mk_range
                                                             "Prims.fst"
                                                             (Prims.of_int (611))
                                                             (Prims.of_int (19))
                                                             (Prims.of_int (611))
                                                             (Prims.of_int (31)))))
                                                    (Obj.magic uu___10)
                                                    (fun uu___11 ->
                                                       FStar_Tactics_Effect.lift_div_tac
                                                         (fun uu___12 ->
                                                            Prims.strcat
                                                              "; type is "
                                                              uu___11)) in
                                                FStar_Tactics_Effect.tac_bind
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "FStar.Tactics.PatternMatching.fst"
                                                           (Prims.of_int (641))
                                                           (Prims.of_int (42))
                                                           (Prims.of_int (642))
                                                           (Prims.of_int (59)))))
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "Prims.fst"
                                                           (Prims.of_int (611))
                                                           (Prims.of_int (19))
                                                           (Prims.of_int (611))
                                                           (Prims.of_int (31)))))
                                                  (Obj.magic uu___9)
                                                  (fun uu___10 ->
                                                     FStar_Tactics_Effect.lift_div_tac
                                                       (fun uu___11 ->
                                                          Prims.strcat
                                                            bv_name uu___10)) in
                                              FStar_Tactics_Effect.tac_bind
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "FStar.Tactics.PatternMatching.fst"
                                                         (Prims.of_int (641))
                                                         (Prims.of_int (32))
                                                         (Prims.of_int (642))
                                                         (Prims.of_int (59)))))
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
                                                        Prims.strcat
                                                          "Got binder: "
                                                          uu___9)) in
                                            FStar_Tactics_Effect.tac_bind
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "FStar.Tactics.PatternMatching.fst"
                                                       (Prims.of_int (641))
                                                       (Prims.of_int (14))
                                                       (Prims.of_int (642))
                                                       (Prims.of_int (60)))))
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "FStar.Tactics.PatternMatching.fst"
                                                       (Prims.of_int (641))
                                                       (Prims.of_int (8))
                                                       (Prims.of_int (642))
                                                       (Prims.of_int (60)))))
                                              (Obj.magic uu___7)
                                              (fun uu___8 ->
                                                 (fun uu___8 ->
                                                    Obj.magic (debug uu___8))
                                                   uu___8) in
                                          Obj.magic
                                            (FStar_Tactics_Effect.tac_bind
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "FStar.Tactics.PatternMatching.fst"
                                                        (Prims.of_int (641))
                                                        (Prims.of_int (8))
                                                        (Prims.of_int (642))
                                                        (Prims.of_int (60)))))
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "FStar.Tactics.PatternMatching.fst"
                                                        (Prims.of_int (642))
                                                        (Prims.of_int (61))
                                                        (Prims.of_int (644))
                                                        (Prims.of_int (43)))))
                                               (Obj.magic uu___6)
                                               (fun uu___7 ->
                                                  (fun uu___7 ->
                                                     let uu___8 =
                                                       classify_abspat_binder
                                                         binder in
                                                     Obj.magic
                                                       (FStar_Tactics_Effect.tac_bind
                                                          (FStar_Sealed.seal
                                                             (Obj.magic
                                                                (FStar_Range.mk_range
                                                                   "FStar.Tactics.PatternMatching.fst"
                                                                   (Prims.of_int (643))
                                                                   (Prims.of_int (31))
                                                                   (Prims.of_int (643))
                                                                   (Prims.of_int (60)))))
                                                          (FStar_Sealed.seal
                                                             (Obj.magic
                                                                (FStar_Range.mk_range
                                                                   "FStar.Tactics.PatternMatching.fst"
                                                                   (Prims.of_int (642))
                                                                   (Prims.of_int (61))
                                                                   (Prims.of_int (644))
                                                                   (Prims.of_int (43)))))
                                                          (Obj.magic uu___8)
                                                          (fun uu___9 ->
                                                             FStar_Tactics_Effect.lift_div_tac
                                                               (fun uu___10
                                                                  ->
                                                                  match uu___9
                                                                  with
                                                                  | (binder_kind,
                                                                    typ) ->
                                                                    (binder,
                                                                    bv_name,
                                                                    binder_kind,
                                                                    typ)))))
                                                    uu___7))) uu___6))
                               binders in
                           Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "FStar.Tactics.PatternMatching.fst"
                                         (Prims.of_int (639))
                                         (Prims.of_int (4))
                                         (Prims.of_int (645))
                                         (Prims.of_int (13)))))
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "FStar.Tactics.PatternMatching.fst"
                                         (Prims.of_int (645))
                                         (Prims.of_int (16))
                                         (Prims.of_int (673))
                                         (Prims.of_int (18)))))
                                (Obj.magic uu___4)
                                (fun uu___5 ->
                                   (fun classified_binders ->
                                      let uu___5 =
                                        FStar_Tactics_Util.fold_left
                                          (fun problem ->
                                             fun uu___6 ->
                                               match uu___6 with
                                               | (binder, bv_name,
                                                  binder_kind, typ) ->
                                                   let uu___7 =
                                                     let uu___8 =
                                                       let uu___9 =
                                                         let uu___10 =
                                                           name_of_named_binder
                                                             binder in
                                                         FStar_Tactics_Effect.tac_bind
                                                           (FStar_Sealed.seal
                                                              (Obj.magic
                                                                 (FStar_Range.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (650))
                                                                    (Prims.of_int (38))
                                                                    (Prims.of_int (650))
                                                                    (Prims.of_int (65)))))
                                                           (FStar_Sealed.seal
                                                              (Obj.magic
                                                                 (FStar_Range.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (650))
                                                                    (Prims.of_int (38))
                                                                    (Prims.of_int (652))
                                                                    (Prims.of_int (51)))))
                                                           (Obj.magic uu___10)
                                                           (fun uu___11 ->
                                                              (fun uu___11 ->
                                                                 let uu___12
                                                                   =
                                                                   let uu___13
                                                                    =
                                                                    let uu___14
                                                                    =
                                                                    let uu___15
                                                                    =
                                                                    FStarC_Tactics_V2_Builtins.term_to_string
                                                                    typ in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (652))
                                                                    (Prims.of_int (33))
                                                                    (Prims.of_int (652))
                                                                    (Prims.of_int (51)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___15)
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___17
                                                                    ->
                                                                    Prims.strcat
                                                                    ", with type "
                                                                    uu___16)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (652))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (652))
                                                                    (Prims.of_int (51)))))
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
                                                                    (string_of_abspat_binder_kind
                                                                    binder_kind)
                                                                    uu___15)) in
                                                                   FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (651))
                                                                    (Prims.of_int (37))
                                                                    (Prims.of_int (652))
                                                                    (Prims.of_int (51)))))
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
                                                                    ", classified as "
                                                                    uu___14)) in
                                                                 Obj.magic
                                                                   (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (651))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (652))
                                                                    (Prims.of_int (51)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___12)
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    Prims.strcat
                                                                    uu___11
                                                                    uu___13))))
                                                                uu___11) in
                                                       FStar_Tactics_Effect.tac_bind
                                                         (FStar_Sealed.seal
                                                            (Obj.magic
                                                               (FStar_Range.mk_range
                                                                  "FStar.Tactics.PatternMatching.fst"
                                                                  (Prims.of_int (650))
                                                                  (Prims.of_int (38))
                                                                  (Prims.of_int (652))
                                                                  (Prims.of_int (51)))))
                                                         (FStar_Sealed.seal
                                                            (Obj.magic
                                                               (FStar_Range.mk_range
                                                                  "Prims.fst"
                                                                  (Prims.of_int (611))
                                                                  (Prims.of_int (19))
                                                                  (Prims.of_int (611))
                                                                  (Prims.of_int (31)))))
                                                         (Obj.magic uu___9)
                                                         (fun uu___10 ->
                                                            FStar_Tactics_Effect.lift_div_tac
                                                              (fun uu___11 ->
                                                                 Prims.strcat
                                                                   "Compiling binder "
                                                                   uu___10)) in
                                                     FStar_Tactics_Effect.tac_bind
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "FStar.Tactics.PatternMatching.fst"
                                                                (Prims.of_int (650))
                                                                (Prims.of_int (15))
                                                                (Prims.of_int (652))
                                                                (Prims.of_int (52)))))
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "FStar.Tactics.PatternMatching.fst"
                                                                (Prims.of_int (650))
                                                                (Prims.of_int (9))
                                                                (Prims.of_int (652))
                                                                (Prims.of_int (52)))))
                                                       (Obj.magic uu___8)
                                                       (fun uu___9 ->
                                                          (fun uu___9 ->
                                                             Obj.magic
                                                               (debug uu___9))
                                                            uu___9) in
                                                   FStar_Tactics_Effect.tac_bind
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "FStar.Tactics.PatternMatching.fst"
                                                              (Prims.of_int (650))
                                                              (Prims.of_int (9))
                                                              (Prims.of_int (652))
                                                              (Prims.of_int (52)))))
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "FStar.Tactics.PatternMatching.fst"
                                                              (Prims.of_int (653))
                                                              (Prims.of_int (9))
                                                              (Prims.of_int (657))
                                                              (Prims.of_int (75)))))
                                                     (Obj.magic uu___7)
                                                     (fun uu___8 ->
                                                        (fun uu___8 ->
                                                           match binder_kind
                                                           with
                                                           | ABKVar uu___9 ->
                                                               Obj.magic
                                                                 (Obj.repr
                                                                    (
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    ->
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
                                                                    (
                                                                    let uu___9
                                                                    =
                                                                    let uu___10
                                                                    =
                                                                    let uu___11
                                                                    =
                                                                    pattern_of_term
                                                                    typ in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (655))
                                                                    (Prims.of_int (56))
                                                                    (Prims.of_int (655))
                                                                    (Prims.of_int (77)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (655))
                                                                    (Prims.of_int (46))
                                                                    (Prims.of_int (655))
                                                                    (Prims.of_int (78)))))
                                                                    (Obj.magic
                                                                    uu___11)
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    (bv_name,
                                                                    uu___12))) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (655))
                                                                    (Prims.of_int (46))
                                                                    (Prims.of_int (655))
                                                                    (Prims.of_int (78)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (655))
                                                                    (Prims.of_int (46))
                                                                    (Prims.of_int (656))
                                                                    (Prims.of_int (63)))))
                                                                    (Obj.magic
                                                                    uu___10)
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    uu___11
                                                                    ::
                                                                    (problem.mp_hyps))) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (655))
                                                                    (Prims.of_int (46))
                                                                    (Prims.of_int (656))
                                                                    (Prims.of_int (63)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (655))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (656))
                                                                    (Prims.of_int (63)))))
                                                                    (Obj.magic
                                                                    uu___9)
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    {
                                                                    mp_vars =
                                                                    (problem.mp_vars);
                                                                    mp_hyps =
                                                                    uu___10;
                                                                    mp_goal =
                                                                    (problem.mp_goal)
                                                                    }))))
                                                           | ABKGoal ->
                                                               Obj.magic
                                                                 (Obj.repr
                                                                    (
                                                                    let uu___9
                                                                    =
                                                                    let uu___10
                                                                    =
                                                                    pattern_of_term
                                                                    typ in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (657))
                                                                    (Prims.of_int (52))
                                                                    (Prims.of_int (657))
                                                                    (Prims.of_int (73)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (657))
                                                                    (Prims.of_int (47))
                                                                    (Prims.of_int (657))
                                                                    (Prims.of_int (73)))))
                                                                    (Obj.magic
                                                                    uu___10)
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    FStar_Pervasives_Native.Some
                                                                    uu___11)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (657))
                                                                    (Prims.of_int (47))
                                                                    (Prims.of_int (657))
                                                                    (Prims.of_int (73)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (657))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (657))
                                                                    (Prims.of_int (73)))))
                                                                    (Obj.magic
                                                                    uu___9)
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    {
                                                                    mp_vars =
                                                                    (problem.mp_vars);
                                                                    mp_hyps =
                                                                    (problem.mp_hyps);
                                                                    mp_goal =
                                                                    uu___10
                                                                    })))))
                                                          uu___8))
                                          {
                                            mp_vars = [];
                                            mp_hyps = [];
                                            mp_goal =
                                              FStar_Pervasives_Native.None
                                          } classified_binders in
                                      Obj.magic
                                        (FStar_Tactics_Effect.tac_bind
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "FStar.Tactics.PatternMatching.fst"
                                                    (Prims.of_int (648))
                                                    (Prims.of_int (4))
                                                    (Prims.of_int (659))
                                                    (Prims.of_int (24)))))
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "FStar.Tactics.PatternMatching.fst"
                                                    (Prims.of_int (659))
                                                    (Prims.of_int (27))
                                                    (Prims.of_int (673))
                                                    (Prims.of_int (18)))))
                                           (Obj.magic uu___5)
                                           (fun uu___6 ->
                                              (fun problem ->
                                                 let uu___6 =
                                                   let uu___7 =
                                                     Obj.magic
                                                       (FStar_Tactics_Effect.lift_div_tac
                                                          (fun uu___9 ->
                                                             fun uu___8 ->
                                                               (fun uu___8 ->
                                                                  fun xx ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    match xx
                                                                    with
                                                                    | 
                                                                    (binder,
                                                                    xx1,
                                                                    binder_kind,
                                                                    yy) ->
                                                                    {
                                                                    asa_name
                                                                    =
                                                                    (FStar_Tactics_NamedView.binder_to_binding
                                                                    binder);
                                                                    asa_kind
                                                                    =
                                                                    binder_kind
                                                                    })))
                                                                 uu___9
                                                                 uu___8)) in
                                                   FStar_Tactics_Effect.tac_bind
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "FStar.Tactics.PatternMatching.fst"
                                                              (Prims.of_int (663))
                                                              (Prims.of_int (4))
                                                              (Prims.of_int (664))
                                                              (Prims.of_int (69)))))
                                                     (FStar_Sealed.seal
                                                        (Obj.magic
                                                           (FStar_Range.mk_range
                                                              "FStar.Tactics.PatternMatching.fst"
                                                              (Prims.of_int (665))
                                                              (Prims.of_int (4))
                                                              (Prims.of_int (665))
                                                              (Prims.of_int (57)))))
                                                     (Obj.magic uu___7)
                                                     (fun uu___8 ->
                                                        (fun
                                                           abspat_argspec_of_binder
                                                           ->
                                                           let uu___8 =
                                                             FStar_Tactics_Util.map
                                                               abspat_argspec_of_binder
                                                               classified_binders in
                                                           Obj.magic
                                                             (FStar_Tactics_Effect.tac_bind
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (665))
                                                                    (Prims.of_int (5))
                                                                    (Prims.of_int (665))
                                                                    (Prims.of_int (52)))))
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (665))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (665))
                                                                    (Prims.of_int (57)))))
                                                                (Obj.magic
                                                                   uu___8)
                                                                (fun uu___9
                                                                   ->
                                                                   FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (uu___9,
                                                                    tm)))))
                                                          uu___8) in
                                                 Obj.magic
                                                   (FStar_Tactics_Effect.tac_bind
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "FStar.Tactics.PatternMatching.fst"
                                                               (Prims.of_int (661))
                                                               (Prims.of_int (20))
                                                               (Prims.of_int (665))
                                                               (Prims.of_int (57)))))
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "FStar.Tactics.PatternMatching.fst"
                                                               (Prims.of_int (665))
                                                               (Prims.of_int (60))
                                                               (Prims.of_int (673))
                                                               (Prims.of_int (18)))))
                                                      (Obj.magic uu___6)
                                                      (fun uu___7 ->
                                                         (fun continuation ->
                                                            let uu___7 =
                                                              Obj.magic
                                                                (FStar_Tactics_Effect.lift_div_tac
                                                                   (fun
                                                                    uu___8 ->
                                                                    {
                                                                    mp_vars =
                                                                    (FStar_List_Tot_Base.rev
                                                                    problem.mp_vars);
                                                                    mp_hyps =
                                                                    (FStar_List_Tot_Base.rev
                                                                    problem.mp_hyps);
                                                                    mp_goal =
                                                                    (problem.mp_goal)
                                                                    })) in
                                                            Obj.magic
                                                              (FStar_Tactics_Effect.tac_bind
                                                                 (FStar_Sealed.seal
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (668))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (670))
                                                                    (Prims.of_int (31)))))
                                                                 (FStar_Sealed.seal
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (672))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (673))
                                                                    (Prims.of_int (18)))))
                                                                 (Obj.magic
                                                                    uu___7)
                                                                 (fun uu___8
                                                                    ->
                                                                    (fun mp
                                                                    ->
                                                                    let uu___8
                                                                    =
                                                                    debug
                                                                    (Prims.strcat
                                                                    "Got matching problem: "
                                                                    (string_of_matching_problem
                                                                    mp)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (672))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (672))
                                                                    (Prims.of_int (68)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (673))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (673))
                                                                    (Prims.of_int (18)))))
                                                                    (Obj.magic
                                                                    uu___8)
                                                                    (fun
                                                                    uu___9 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (mp,
                                                                    continuation)))))
                                                                    uu___8)))
                                                           uu___7))) uu___6)))
                                     uu___5))) uu___3))) uu___1)
let (arg_type_of_binder_kind :
  abspat_binder_kind ->
    (FStar_Tactics_NamedView.term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___ ->
    (fun binder_kind ->
       Obj.magic
         (FStar_Tactics_Effect.lift_div_tac
            (fun uu___ ->
               match binder_kind with
               | ABKVar typ -> typ
               | ABKHyp ->
                   FStarC_Reflection_V2_Builtins.pack_ln
                     (FStarC_Reflection_V2_Data.Tv_FVar
                        (FStarC_Reflection_V2_Builtins.pack_fv
                           ["FStar"; "Tactics"; "NamedView"; "binder"]))
               | ABKGoal ->
                   FStarC_Reflection_V2_Builtins.pack_ln
                     (FStarC_Reflection_V2_Data.Tv_FVar
                        (FStarC_Reflection_V2_Builtins.pack_fv
                           ["Prims"; "unit"]))))) uu___
let (locate_fn_of_binder_kind :
  abspat_binder_kind -> FStarC_Reflection_Types.term) =
  fun binder_kind ->
    match binder_kind with
    | ABKVar uu___ ->
        FStarC_Reflection_V2_Builtins.pack_ln
          (FStarC_Reflection_V2_Data.Tv_FVar
             (FStarC_Reflection_V2_Builtins.pack_fv
                ["FStar"; "Tactics"; "PatternMatching"; "ms_locate_var"]))
    | ABKHyp ->
        FStarC_Reflection_V2_Builtins.pack_ln
          (FStarC_Reflection_V2_Data.Tv_FVar
             (FStarC_Reflection_V2_Builtins.pack_fv
                ["FStar"; "Tactics"; "PatternMatching"; "ms_locate_hyp"]))
    | ABKGoal ->
        FStarC_Reflection_V2_Builtins.pack_ln
          (FStarC_Reflection_V2_Data.Tv_FVar
             (FStarC_Reflection_V2_Builtins.pack_fv
                ["FStar"; "Tactics"; "PatternMatching"; "ms_locate_unit"]))
let (abspat_arg_of_abspat_argspec :
  FStarC_Reflection_Types.term ->
    abspat_argspec ->
      (FStar_Tactics_NamedView.term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun solution_term ->
    fun argspec ->
      let uu___ =
        Obj.magic
          (FStar_Tactics_Effect.lift_div_tac
             (fun uu___1 -> locate_fn_of_binder_kind argspec.asa_kind)) in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.PatternMatching.fst"
                 (Prims.of_int (700)) (Prims.of_int (15))
                 (Prims.of_int (700)) (Prims.of_int (56)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.PatternMatching.fst"
                 (Prims.of_int (700)) (Prims.of_int (59))
                 (Prims.of_int (704)) (Prims.of_int (27)))))
        (Obj.magic uu___)
        (fun uu___1 ->
           (fun loc_fn ->
              let uu___1 =
                let uu___2 =
                  let uu___3 =
                    let uu___4 =
                      FStarC_Tactics_Unseal.unseal
                        (argspec.asa_name).FStarC_Reflection_V2_Data.ppname3 in
                    FStar_Tactics_Effect.tac_bind
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range
                               "FStar.Tactics.PatternMatching.fst"
                               (Prims.of_int (701)) (Prims.of_int (41))
                               (Prims.of_int (701)) (Prims.of_int (73)))))
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range
                               "FStar.Tactics.PatternMatching.fst"
                               (Prims.of_int (701)) (Prims.of_int (31))
                               (Prims.of_int (701)) (Prims.of_int (74)))))
                      (Obj.magic uu___4)
                      (fun uu___5 ->
                         FStar_Tactics_Effect.lift_div_tac
                           (fun uu___6 ->
                              FStarC_Reflection_V2_Data.C_String uu___5)) in
                  FStar_Tactics_Effect.tac_bind
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range
                             "FStar.Tactics.PatternMatching.fst"
                             (Prims.of_int (701)) (Prims.of_int (31))
                             (Prims.of_int (701)) (Prims.of_int (74)))))
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range
                             "FStar.Tactics.PatternMatching.fst"
                             (Prims.of_int (701)) (Prims.of_int (21))
                             (Prims.of_int (701)) (Prims.of_int (75)))))
                    (Obj.magic uu___3)
                    (fun uu___4 ->
                       FStar_Tactics_Effect.lift_div_tac
                         (fun uu___5 ->
                            FStar_Tactics_NamedView.Tv_Const uu___4)) in
                FStar_Tactics_Effect.tac_bind
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range
                           "FStar.Tactics.PatternMatching.fst"
                           (Prims.of_int (701)) (Prims.of_int (21))
                           (Prims.of_int (701)) (Prims.of_int (75)))))
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range "dummy" Prims.int_zero
                           Prims.int_zero Prims.int_zero Prims.int_zero)))
                  (Obj.magic uu___2)
                  (fun uu___3 ->
                     FStar_Tactics_Effect.lift_div_tac
                       (fun uu___4 -> FStar_Tactics_NamedView.pack uu___3)) in
              Obj.magic
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range
                            "FStar.Tactics.PatternMatching.fst"
                            (Prims.of_int (701)) (Prims.of_int (16))
                            (Prims.of_int (701)) (Prims.of_int (75)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range
                            "FStar.Tactics.PatternMatching.fst"
                            (Prims.of_int (701)) (Prims.of_int (78))
                            (Prims.of_int (704)) (Prims.of_int (27)))))
                   (Obj.magic uu___1)
                   (fun uu___2 ->
                      (fun name_tm ->
                         let uu___2 =
                           let uu___3 =
                             let uu___4 =
                               arg_type_of_binder_kind argspec.asa_kind in
                             FStar_Tactics_Effect.tac_bind
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "FStar.Tactics.PatternMatching.fst"
                                        (Prims.of_int (702))
                                        (Prims.of_int (22))
                                        (Prims.of_int (702))
                                        (Prims.of_int (62)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "FStar.Tactics.PatternMatching.fst"
                                        (Prims.of_int (702))
                                        (Prims.of_int (21))
                                        (Prims.of_int (702))
                                        (Prims.of_int (75)))))
                               (Obj.magic uu___4)
                               (fun uu___5 ->
                                  FStar_Tactics_Effect.lift_div_tac
                                    (fun uu___6 ->
                                       (uu___5,
                                         FStarC_Reflection_V2_Data.Q_Explicit))) in
                           FStar_Tactics_Effect.tac_bind
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "FStar.Tactics.PatternMatching.fst"
                                      (Prims.of_int (702))
                                      (Prims.of_int (21))
                                      (Prims.of_int (702))
                                      (Prims.of_int (75)))))
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "FStar.Tactics.PatternMatching.fst"
                                      (Prims.of_int (702))
                                      (Prims.of_int (20))
                                      (Prims.of_int (703))
                                      (Prims.of_int (72)))))
                             (Obj.magic uu___3)
                             (fun uu___4 ->
                                FStar_Tactics_Effect.lift_div_tac
                                  (fun uu___5 ->
                                     [uu___4;
                                     (solution_term,
                                       FStarC_Reflection_V2_Data.Q_Explicit);
                                     (name_tm,
                                       FStarC_Reflection_V2_Data.Q_Explicit)])) in
                         Obj.magic
                           (FStar_Tactics_Effect.tac_bind
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "FStar.Tactics.PatternMatching.fst"
                                       (Prims.of_int (702))
                                       (Prims.of_int (20))
                                       (Prims.of_int (703))
                                       (Prims.of_int (72)))))
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "FStar.Tactics.PatternMatching.fst"
                                       (Prims.of_int (704))
                                       (Prims.of_int (2))
                                       (Prims.of_int (704))
                                       (Prims.of_int (27)))))
                              (Obj.magic uu___2)
                              (fun locate_args ->
                                 FStar_Tactics_Effect.lift_div_tac
                                   (fun uu___3 ->
                                      FStar_Reflection_V2_Derived.mk_app
                                        loc_fn locate_args)))) uu___2)))
             uu___1)
let rec (hoist_and_apply :
  FStar_Tactics_NamedView.term ->
    FStar_Tactics_NamedView.term Prims.list ->
      FStarC_Reflection_V2_Data.argv Prims.list ->
        (FStar_Tactics_NamedView.term, unit) FStar_Tactics_Effect.tac_repr)
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
                              FStar_Reflection_V2_Derived.mk_app head
                                (FStar_List_Tot_Base.rev hoisted_args))))
               | arg_term::rest ->
                   Obj.magic
                     (Obj.repr
                        (let uu___ =
                           Obj.magic
                             (FStar_Tactics_Effect.lift_div_tac
                                (fun uu___1 ->
                                   FStar_List_Tot_Base.length hoisted_args)) in
                         FStar_Tactics_Effect.tac_bind
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "FStar.Tactics.PatternMatching.fst"
                                    (Prims.of_int (715)) (Prims.of_int (12))
                                    (Prims.of_int (715)) (Prims.of_int (40)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "FStar.Tactics.PatternMatching.fst"
                                    (Prims.of_int (715)) (Prims.of_int (43))
                                    (Prims.of_int (725)) (Prims.of_int (132)))))
                           (Obj.magic uu___)
                           (fun uu___1 ->
                              (fun n ->
                                 let uu___1 =
                                   let uu___2 =
                                     FStarC_Tactics_V2_Builtins.fresh () in
                                   FStar_Tactics_Effect.tac_bind
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "FStar.Tactics.PatternMatching.fst"
                                              (Prims.of_int (720))
                                              (Prims.of_int (13))
                                              (Prims.of_int (720))
                                              (Prims.of_int (21)))))
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "FStar.Tactics.PatternMatching.fst"
                                              (Prims.of_int (718))
                                              (Prims.of_int (6))
                                              (Prims.of_int (722))
                                              (Prims.of_int (18)))))
                                     (Obj.magic uu___2)
                                     (fun uu___3 ->
                                        FStar_Tactics_Effect.lift_div_tac
                                          (fun uu___4 ->
                                             {
                                               FStar_Tactics_NamedView.uniq =
                                                 uu___3;
                                               FStar_Tactics_NamedView.ppname
                                                 =
                                                 (FStar_Sealed.seal
                                                    (Prims.strcat "x"
                                                       (Prims.string_of_int n)));
                                               FStar_Tactics_NamedView.sort =
                                                 (FStarC_Reflection_V2_Builtins.pack_ln
                                                    FStarC_Reflection_V2_Data.Tv_Unknown);
                                               FStar_Tactics_NamedView.qual =
                                                 FStarC_Reflection_V2_Data.Q_Explicit;
                                               FStar_Tactics_NamedView.attrs
                                                 = []
                                             })) in
                                 Obj.magic
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "FStar.Tactics.PatternMatching.fst"
                                               (Prims.of_int (718))
                                               (Prims.of_int (6))
                                               (Prims.of_int (722))
                                               (Prims.of_int (18)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "FStar.Tactics.PatternMatching.fst"
                                               (Prims.of_int (725))
                                               (Prims.of_int (4))
                                               (Prims.of_int (725))
                                               (Prims.of_int (132)))))
                                      (Obj.magic uu___1)
                                      (fun uu___2 ->
                                         (fun nb ->
                                            let uu___2 =
                                              let uu___3 =
                                                hoist_and_apply head rest
                                                  (((FStar_Tactics_NamedView.pack
                                                       (FStar_Tactics_NamedView.Tv_Var
                                                          (FStar_Tactics_V2_SyntaxCoercions.binder_to_namedv
                                                             nb))),
                                                     FStarC_Reflection_V2_Data.Q_Explicit)
                                                  :: hoisted_args) in
                                              FStar_Tactics_Effect.tac_bind
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "FStar.Tactics.PatternMatching.fst"
                                                         (Prims.of_int (725))
                                                         (Prims.of_int (38))
                                                         (Prims.of_int (725))
                                                         (Prims.of_int (131)))))
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "FStar.Tactics.PatternMatching.fst"
                                                         (Prims.of_int (725))
                                                         (Prims.of_int (9))
                                                         (Prims.of_int (725))
                                                         (Prims.of_int (132)))))
                                                (Obj.magic uu___3)
                                                (fun uu___4 ->
                                                   FStar_Tactics_Effect.lift_div_tac
                                                     (fun uu___5 ->
                                                        FStar_Tactics_NamedView.Tv_Let
                                                          (false, [], nb,
                                                            arg_term, uu___4))) in
                                            Obj.magic
                                              (FStar_Tactics_Effect.tac_bind
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "FStar.Tactics.PatternMatching.fst"
                                                          (Prims.of_int (725))
                                                          (Prims.of_int (9))
                                                          (Prims.of_int (725))
                                                          (Prims.of_int (132)))))
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "dummy"
                                                          Prims.int_zero
                                                          Prims.int_zero
                                                          Prims.int_zero
                                                          Prims.int_zero)))
                                                 (Obj.magic uu___2)
                                                 (fun uu___3 ->
                                                    FStar_Tactics_Effect.lift_div_tac
                                                      (fun uu___4 ->
                                                         FStar_Tactics_NamedView.pack
                                                           uu___3)))) uu___2)))
                                uu___1)))) uu___2 uu___1 uu___
let (specialize_abspat_continuation' :
  abspat_continuation ->
    FStar_Tactics_NamedView.term ->
      (FStar_Tactics_NamedView.term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun continuation ->
    fun solution_term ->
      let uu___ =
        Obj.magic
          (FStar_Tactics_Effect.lift_div_tac
             (fun uu___1 ->
                fun argspec ->
                  abspat_arg_of_abspat_argspec solution_term argspec)) in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.PatternMatching.fst"
                 (Prims.of_int (731)) (Prims.of_int (4)) (Prims.of_int (731))
                 (Prims.of_int (54)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.PatternMatching.fst"
                 (Prims.of_int (731)) (Prims.of_int (57))
                 (Prims.of_int (733)) (Prims.of_int (52)))))
        (Obj.magic uu___)
        (fun uu___1 ->
           (fun mk_arg_term ->
              let uu___1 =
                Obj.magic
                  (FStar_Tactics_Effect.lift_div_tac
                     (fun uu___2 -> continuation)) in
              Obj.magic
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range
                            "FStar.Tactics.PatternMatching.fst"
                            (Prims.of_int (732)) (Prims.of_int (23))
                            (Prims.of_int (732)) (Prims.of_int (35)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range
                            "FStar.Tactics.PatternMatching.fst"
                            (Prims.of_int (731)) (Prims.of_int (57))
                            (Prims.of_int (733)) (Prims.of_int (52)))))
                   (Obj.magic uu___1)
                   (fun uu___2 ->
                      (fun uu___2 ->
                         match uu___2 with
                         | (argspecs, body) ->
                             let uu___3 =
                               FStar_Tactics_Util.map mk_arg_term argspecs in
                             Obj.magic
                               (FStar_Tactics_Effect.tac_bind
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "FStar.Tactics.PatternMatching.fst"
                                           (Prims.of_int (733))
                                           (Prims.of_int (23))
                                           (Prims.of_int (733))
                                           (Prims.of_int (49)))))
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "FStar.Tactics.PatternMatching.fst"
                                           (Prims.of_int (733))
                                           (Prims.of_int (2))
                                           (Prims.of_int (733))
                                           (Prims.of_int (52)))))
                                  (Obj.magic uu___3)
                                  (fun uu___4 ->
                                     (fun uu___4 ->
                                        Obj.magic
                                          (hoist_and_apply body uu___4 []))
                                       uu___4))) uu___2))) uu___1)
let (specialize_abspat_continuation :
  abspat_continuation ->
    (FStar_Tactics_NamedView.term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun continuation ->
    let uu___ =
      FStar_Tactics_V2_Derived.fresh_binder
        (FStarC_Reflection_V2_Builtins.pack_ln
           (FStarC_Reflection_V2_Data.Tv_FVar
              (FStarC_Reflection_V2_Builtins.pack_fv
                 ["FStar"; "Tactics"; "PatternMatching"; "matching_solution"]))) in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.PatternMatching.fst"
               (Prims.of_int (740)) (Prims.of_int (24)) (Prims.of_int (740))
               (Prims.of_int (57)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.PatternMatching.fst"
               (Prims.of_int (740)) (Prims.of_int (60)) (Prims.of_int (747))
               (Prims.of_int (9))))) (Obj.magic uu___)
      (fun uu___1 ->
         (fun solution_binder ->
            let uu___1 =
              Obj.magic
                (FStar_Tactics_Effect.lift_div_tac
                   (fun uu___2 ->
                      FStar_Tactics_NamedView.pack
                        (FStar_Tactics_NamedView.Tv_Var
                           (FStar_Tactics_V2_SyntaxCoercions.binder_to_namedv
                              solution_binder)))) in
            Obj.magic
              (FStar_Tactics_Effect.tac_bind
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range
                          "FStar.Tactics.PatternMatching.fst"
                          (Prims.of_int (741)) (Prims.of_int (22))
                          (Prims.of_int (741)) (Prims.of_int (70)))))
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range
                          "FStar.Tactics.PatternMatching.fst"
                          (Prims.of_int (741)) (Prims.of_int (73))
                          (Prims.of_int (747)) (Prims.of_int (9)))))
                 (Obj.magic uu___1)
                 (fun uu___2 ->
                    (fun solution_term ->
                       let uu___2 =
                         specialize_abspat_continuation' continuation
                           solution_term in
                       Obj.magic
                         (FStar_Tactics_Effect.tac_bind
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.PatternMatching.fst"
                                     (Prims.of_int (742)) (Prims.of_int (16))
                                     (Prims.of_int (742)) (Prims.of_int (74)))))
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.PatternMatching.fst"
                                     (Prims.of_int (742)) (Prims.of_int (77))
                                     (Prims.of_int (747)) (Prims.of_int (9)))))
                            (Obj.magic uu___2)
                            (fun uu___3 ->
                               (fun applied ->
                                  let uu___3 =
                                    Obj.magic
                                      (FStar_Tactics_Effect.lift_div_tac
                                         (fun uu___4 ->
                                            FStar_Tactics_NamedView.pack
                                              (FStar_Tactics_NamedView.Tv_Abs
                                                 (solution_binder, applied)))) in
                                  Obj.magic
                                    (FStar_Tactics_Effect.tac_bind
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "FStar.Tactics.PatternMatching.fst"
                                                (Prims.of_int (743))
                                                (Prims.of_int (16))
                                                (Prims.of_int (743))
                                                (Prims.of_int (53)))))
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "FStar.Tactics.PatternMatching.fst"
                                                (Prims.of_int (744))
                                                (Prims.of_int (2))
                                                (Prims.of_int (747))
                                                (Prims.of_int (9)))))
                                       (Obj.magic uu___3)
                                       (fun uu___4 ->
                                          (fun thunked ->
                                             let uu___4 =
                                               let uu___5 =
                                                 let uu___6 =
                                                   FStarC_Tactics_V2_Builtins.term_to_string
                                                     thunked in
                                                 FStar_Tactics_Effect.tac_bind
                                                   (FStar_Sealed.seal
                                                      (Obj.magic
                                                         (FStar_Range.mk_range
                                                            "FStar.Tactics.PatternMatching.fst"
                                                            (Prims.of_int (744))
                                                            (Prims.of_int (31))
                                                            (Prims.of_int (744))
                                                            (Prims.of_int (55)))))
                                                   (FStar_Sealed.seal
                                                      (Obj.magic
                                                         (FStar_Range.mk_range
                                                            "Prims.fst"
                                                            (Prims.of_int (611))
                                                            (Prims.of_int (19))
                                                            (Prims.of_int (611))
                                                            (Prims.of_int (31)))))
                                                   (Obj.magic uu___6)
                                                   (fun uu___7 ->
                                                      FStar_Tactics_Effect.lift_div_tac
                                                        (fun uu___8 ->
                                                           Prims.strcat
                                                             "Specialized into "
                                                             uu___7)) in
                                               FStar_Tactics_Effect.tac_bind
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "FStar.Tactics.PatternMatching.fst"
                                                          (Prims.of_int (744))
                                                          (Prims.of_int (8))
                                                          (Prims.of_int (744))
                                                          (Prims.of_int (56)))))
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "FStar.Tactics.PatternMatching.fst"
                                                          (Prims.of_int (744))
                                                          (Prims.of_int (2))
                                                          (Prims.of_int (744))
                                                          (Prims.of_int (56)))))
                                                 (Obj.magic uu___5)
                                                 (fun uu___6 ->
                                                    (fun uu___6 ->
                                                       Obj.magic
                                                         (debug uu___6))
                                                      uu___6) in
                                             Obj.magic
                                               (FStar_Tactics_Effect.tac_bind
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "FStar.Tactics.PatternMatching.fst"
                                                           (Prims.of_int (744))
                                                           (Prims.of_int (2))
                                                           (Prims.of_int (744))
                                                           (Prims.of_int (56)))))
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "FStar.Tactics.PatternMatching.fst"
                                                           (Prims.of_int (744))
                                                           (Prims.of_int (57))
                                                           (Prims.of_int (747))
                                                           (Prims.of_int (9)))))
                                                  (Obj.magic uu___4)
                                                  (fun uu___5 ->
                                                     (fun uu___5 ->
                                                        let uu___6 =
                                                          beta_reduce thunked in
                                                        Obj.magic
                                                          (FStar_Tactics_Effect.tac_bind
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (745))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (745))
                                                                    (Prims.of_int (38)))))
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (746))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (747))
                                                                    (Prims.of_int (9)))))
                                                             (Obj.magic
                                                                uu___6)
                                                             (fun uu___7 ->
                                                                (fun
                                                                   normalized
                                                                   ->
                                                                   let uu___7
                                                                    =
                                                                    let uu___8
                                                                    =
                                                                    let uu___9
                                                                    =
                                                                    FStarC_Tactics_V2_Builtins.term_to_string
                                                                    normalized in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (746))
                                                                    (Prims.of_int (33))
                                                                    (Prims.of_int (746))
                                                                    (Prims.of_int (60)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___9)
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    Prims.strcat
                                                                    "\226\128\166 which reduces to "
                                                                    uu___10)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (746))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (746))
                                                                    (Prims.of_int (61)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (746))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (746))
                                                                    (Prims.of_int (61)))))
                                                                    (Obj.magic
                                                                    uu___8)
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun
                                                                    uu___9 ->
                                                                    Obj.magic
                                                                    (debug
                                                                    uu___9))
                                                                    uu___9) in
                                                                   Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (746))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (746))
                                                                    (Prims.of_int (61)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.PatternMatching.fst"
                                                                    (Prims.of_int (743))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (743))
                                                                    (Prims.of_int (13)))))
                                                                    (Obj.magic
                                                                    uu___7)
                                                                    (fun
                                                                    uu___8 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    thunked))))
                                                                  uu___7)))
                                                       uu___5))) uu___4)))
                                 uu___3))) uu___2))) uu___1)
let interp_abspat_continuation :
  'a .
    abspat_continuation ->
      (matching_solution -> ('a, unit) FStar_Tactics_Effect.tac_repr, 
        unit) FStar_Tactics_Effect.tac_repr
  =
  fun continuation ->
    let uu___ = specialize_abspat_continuation continuation in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.PatternMatching.fst"
               (Prims.of_int (754)) (Prims.of_int (16)) (Prims.of_int (754))
               (Prims.of_int (59)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.PatternMatching.fst"
               (Prims.of_int (755)) (Prims.of_int (2)) (Prims.of_int (755))
               (Prims.of_int (47))))) (Obj.magic uu___)
      (fun uu___1 ->
         (fun applied ->
            Obj.magic (FStarC_Tactics_V2_Builtins.unquote applied)) uu___1)
let interp_abspat :
  'a .
    'a ->
      ((matching_problem * abspat_continuation), unit)
        FStar_Tactics_Effect.tac_repr
  =
  fun abspat ->
    let uu___ =
      Obj.magic
        (FStar_Tactics_Effect.lift_div_tac
           (fun uu___1 ->
              (fun uu___1 ->
                 Obj.magic
                   (failwith "Cannot evaluate open quotation at runtime"))
                uu___1)) in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.PatternMatching.fst"
               (Prims.of_int (765)) (Prims.of_int (26)) (Prims.of_int (765))
               (Prims.of_int (40)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.PatternMatching.fst"
               (Prims.of_int (765)) (Prims.of_int (2)) (Prims.of_int (765))
               (Prims.of_int (40))))) (Obj.magic uu___)
      (fun uu___1 ->
         (fun uu___1 -> Obj.magic (matching_problem_of_abs uu___1)) uu___1)
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
      let uu___ = FStar_Tactics_V2_Derived.cur_goal () in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.PatternMatching.fst"
                 (Prims.of_int (773)) (Prims.of_int (13))
                 (Prims.of_int (773)) (Prims.of_int (24)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.PatternMatching.fst"
                 (Prims.of_int (773)) (Prims.of_int (27))
                 (Prims.of_int (776)) (Prims.of_int (51)))))
        (Obj.magic uu___)
        (fun uu___1 ->
           (fun goal ->
              let uu___1 =
                let uu___2 = FStar_Tactics_V2_Derived.cur_env () in
                FStar_Tactics_Effect.tac_bind
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range
                           "FStar.Tactics.PatternMatching.fst"
                           (Prims.of_int (774)) (Prims.of_int (31))
                           (Prims.of_int (774)) (Prims.of_int (43)))))
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range
                           "FStar.Tactics.PatternMatching.fst"
                           (Prims.of_int (774)) (Prims.of_int (19))
                           (Prims.of_int (774)) (Prims.of_int (43)))))
                  (Obj.magic uu___2)
                  (fun uu___3 ->
                     FStar_Tactics_Effect.lift_div_tac
                       (fun uu___4 ->
                          FStarC_Reflection_V2_Builtins.vars_of_env uu___3)) in
              Obj.magic
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range
                            "FStar.Tactics.PatternMatching.fst"
                            (Prims.of_int (774)) (Prims.of_int (19))
                            (Prims.of_int (774)) (Prims.of_int (43)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range
                            "FStar.Tactics.PatternMatching.fst"
                            (Prims.of_int (774)) (Prims.of_int (46))
                            (Prims.of_int (776)) (Prims.of_int (51)))))
                   (Obj.magic uu___1)
                   (fun uu___2 ->
                      (fun hypotheses ->
                         let uu___2 = interp_abspat abspat in
                         Obj.magic
                           (FStar_Tactics_Effect.tac_bind
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "FStar.Tactics.PatternMatching.fst"
                                       (Prims.of_int (775))
                                       (Prims.of_int (30))
                                       (Prims.of_int (775))
                                       (Prims.of_int (50)))))
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "FStar.Tactics.PatternMatching.fst"
                                       (Prims.of_int (774))
                                       (Prims.of_int (46))
                                       (Prims.of_int (776))
                                       (Prims.of_int (51)))))
                              (Obj.magic uu___2)
                              (fun uu___3 ->
                                 (fun uu___3 ->
                                    match uu___3 with
                                    | (problem, continuation) ->
                                        let uu___4 = k continuation in
                                        Obj.magic
                                          (FStar_Tactics_Effect.tac_bind
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "FStar.Tactics.PatternMatching.fst"
                                                      (Prims.of_int (776))
                                                      (Prims.of_int (35))
                                                      (Prims.of_int (776))
                                                      (Prims.of_int (51)))))
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "FStar.Tactics.PatternMatching.fst"
                                                      (Prims.of_int (776))
                                                      (Prims.of_int (2))
                                                      (Prims.of_int (776))
                                                      (Prims.of_int (51)))))
                                             (Obj.magic uu___4)
                                             (fun uu___5 ->
                                                (fun uu___5 ->
                                                   Obj.magic
                                                     (solve_mp problem
                                                        hypotheses goal
                                                        uu___5)) uu___5)))
                                   uu___3))) uu___2))) uu___1)
let inspect_abspat_problem :
  'a . 'a -> (matching_problem, unit) FStar_Tactics_Effect.tac_repr =
  fun abspat ->
    let uu___ = interp_abspat abspat in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.PatternMatching.fst"
               (Prims.of_int (780)) (Prims.of_int (6)) (Prims.of_int (780))
               (Prims.of_int (31)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.PatternMatching.fst"
               (Prims.of_int (780)) (Prims.of_int (2)) (Prims.of_int (780))
               (Prims.of_int (31))))) (Obj.magic uu___)
      (fun uu___1 ->
         FStar_Tactics_Effect.lift_div_tac
           (fun uu___2 -> FStar_Pervasives_Native.fst uu___1))
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
      let uu___1 = match_abspat abspat tpair in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.PatternMatching.fst"
                 (Prims.of_int (804)) (Prims.of_int (31))
                 (Prims.of_int (804)) (Prims.of_int (56)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.PatternMatching.fst"
                 (Prims.of_int (803)) (Prims.of_int (38))
                 (Prims.of_int (805)) (Prims.of_int (52)))))
        (Obj.magic uu___1)
        (fun uu___2 ->
           (fun uu___2 ->
              match uu___2 with
              | (continuation, solution) ->
                  let uu___3 = interp_abspat_continuation continuation in
                  Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "FStar.Tactics.PatternMatching.fst"
                                (Prims.of_int (805)) (Prims.of_int (2))
                                (Prims.of_int (805)) (Prims.of_int (52)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "FStar.Tactics.PatternMatching.fst"
                                (Prims.of_int (805)) (Prims.of_int (2))
                                (Prims.of_int (805)) (Prims.of_int (52)))))
                       (Obj.magic uu___3)
                       (fun uu___4 ->
                          (fun uu___4 -> Obj.magic (uu___4 solution)) uu___4)))
             uu___2)
let pm : 'b 'a . 'a -> ('b, unit) FStar_Tactics_Effect.tac_repr =
  fun abspat -> match_abspat abspat interp_abspat_continuation
let fetch_eq_side' :
  'a . unit -> (FStar_Tactics_NamedView.term * FStar_Tactics_NamedView.term)
  =
  fun uu___ ->
    (fun uu___ ->
       Obj.magic
         (gpm
            (fun left ->
               fun right ->
                 fun g ->
                   let uu___1 =
                     Obj.magic
                       (FStar_Tactics_Effect.lift_div_tac
                          (fun uu___2 ->
                             (fun uu___2 ->
                                Obj.magic
                                  (failwith
                                     "Cannot evaluate open quotation at runtime"))
                               uu___2)) in
                   FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "FStar.Tactics.PatternMatching.fst"
                              (Prims.of_int (828)) (Prims.of_int (10))
                              (Prims.of_int (828)) (Prims.of_int (20)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "FStar.Tactics.PatternMatching.fst"
                              (Prims.of_int (828)) (Prims.of_int (9))
                              (Prims.of_int (828)) (Prims.of_int (34)))))
                     (Obj.magic uu___1)
                     (fun uu___2 ->
                        (fun uu___2 ->
                           let uu___3 =
                             Obj.magic
                               (FStar_Tactics_Effect.lift_div_tac
                                  (fun uu___4 ->
                                     (fun uu___4 ->
                                        Obj.magic
                                          (failwith
                                             "Cannot evaluate open quotation at runtime"))
                                       uu___4)) in
                           Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "FStar.Tactics.PatternMatching.fst"
                                         (Prims.of_int (828))
                                         (Prims.of_int (22))
                                         (Prims.of_int (828))
                                         (Prims.of_int (33)))))
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "FStar.Tactics.PatternMatching.fst"
                                         (Prims.of_int (828))
                                         (Prims.of_int (9))
                                         (Prims.of_int (828))
                                         (Prims.of_int (34)))))
                                (Obj.magic uu___3)
                                (fun uu___4 ->
                                   FStar_Tactics_Effect.lift_div_tac
                                     (fun uu___5 -> (uu___2, uu___4)))))
                          uu___2)) ())) uu___