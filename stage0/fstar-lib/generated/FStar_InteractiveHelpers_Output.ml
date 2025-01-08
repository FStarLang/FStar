open Prims
let rec _split_subst_at_bv :
  'a 'b .
    FStarC_Reflection_Types.bv ->
      ((FStarC_Reflection_Types.bv * 'a) * 'b) Prims.list ->
        (((FStarC_Reflection_Types.bv * 'a) * 'b) Prims.list *
          ((FStarC_Reflection_Types.bv * 'a) * 'b) Prims.list)
  =
  fun x ->
    fun subst ->
      match subst with
      | [] -> ([], [])
      | ((src, ty), tgt)::subst' ->
          if FStar_InteractiveHelpers_Base.bv_eq x src
          then ([], subst')
          else
            (let uu___1 = _split_subst_at_bv x subst' in
             match uu___1 with | (s1, s2) -> ((((src, ty), tgt) :: s1), s2))
let (subst_shadowed_with_abs_in_assertions :
  Prims.bool ->
    FStar_InteractiveHelpers_Base.genv ->
      FStarC_Reflection_Types.bv FStar_Pervasives_Native.option ->
        FStar_InteractiveHelpers_Propositions.assertions ->
          ((FStar_InteractiveHelpers_Base.genv *
             FStar_InteractiveHelpers_Propositions.assertions),
            unit) FStar_Tactics_Effect.tac_repr)
  =
  fun dbg ->
    fun ge ->
      fun shadowed_bv ->
        fun es ->
          let uu___ =
            let uu___1 =
              let uu___2 = FStar_InteractiveHelpers_Base.genv_to_string ge in
              FStar_Tactics_Effect.tac_bind
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range
                         "FStar.InteractiveHelpers.Output.fst"
                         (Prims.of_int (44)) (Prims.of_int (62))
                         (Prims.of_int (44)) (Prims.of_int (79)))))
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Prims.fst" (Prims.of_int (611))
                         (Prims.of_int (19)) (Prims.of_int (611))
                         (Prims.of_int (31))))) (Obj.magic uu___2)
                (fun uu___3 ->
                   FStar_Tactics_Effect.lift_div_tac
                     (fun uu___4 ->
                        Prims.strcat
                          "subst_shadowed_with_abs_in_assertions:\n" uu___3)) in
            FStar_Tactics_Effect.tac_bind
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range
                       "FStar.InteractiveHelpers.Output.fst"
                       (Prims.of_int (44)) (Prims.of_int (16))
                       (Prims.of_int (44)) (Prims.of_int (80)))))
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range
                       "FStar.InteractiveHelpers.Output.fst"
                       (Prims.of_int (44)) (Prims.of_int (2))
                       (Prims.of_int (44)) (Prims.of_int (80)))))
              (Obj.magic uu___1)
              (fun uu___2 ->
                 (fun uu___2 ->
                    Obj.magic
                      (FStar_InteractiveHelpers_Base.print_dbg dbg uu___2))
                   uu___2) in
          FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "FStar.InteractiveHelpers.Output.fst"
                     (Prims.of_int (44)) (Prims.of_int (2))
                     (Prims.of_int (44)) (Prims.of_int (80)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "FStar.InteractiveHelpers.Output.fst"
                     (Prims.of_int (44)) (Prims.of_int (81))
                     (Prims.of_int (73)) (Prims.of_int (31)))))
            (Obj.magic uu___)
            (fun uu___1 ->
               (fun uu___1 ->
                  let uu___2 =
                    FStar_InteractiveHelpers_Base.generate_shadowed_subst ge in
                  Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "FStar.InteractiveHelpers.Output.fst"
                                (Prims.of_int (46)) (Prims.of_int (19))
                                (Prims.of_int (46)) (Prims.of_int (45)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "FStar.InteractiveHelpers.Output.fst"
                                (Prims.of_int (44)) (Prims.of_int (81))
                                (Prims.of_int (73)) (Prims.of_int (31)))))
                       (Obj.magic uu___2)
                       (fun uu___3 ->
                          (fun uu___3 ->
                             match uu___3 with
                             | (ge1, subst) ->
                                 let uu___4 =
                                   FStar_Tactics_Util.map
                                     (fun uu___5 ->
                                        match uu___5 with
                                        | (src, ty, tgt) ->
                                            let uu___6 =
                                              FStarC_Tactics_V1_Builtins.pack
                                                (FStarC_Reflection_V1_Data.Tv_Var
                                                   tgt) in
                                            FStar_Tactics_Effect.tac_bind
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "FStar.InteractiveHelpers.Output.fst"
                                                       (Prims.of_int (47))
                                                       (Prims.of_int (57))
                                                       (Prims.of_int (47))
                                                       (Prims.of_int (74)))))
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "FStar.InteractiveHelpers.Output.fst"
                                                       (Prims.of_int (47))
                                                       (Prims.of_int (46))
                                                       (Prims.of_int (47))
                                                       (Prims.of_int (74)))))
                                              (Obj.magic uu___6)
                                              (fun uu___7 ->
                                                 FStar_Tactics_Effect.lift_div_tac
                                                   (fun uu___8 ->
                                                      ((src, ty), uu___7))))
                                     subst in
                                 Obj.magic
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "FStar.InteractiveHelpers.Output.fst"
                                               (Prims.of_int (47))
                                               (Prims.of_int (19))
                                               (Prims.of_int (47))
                                               (Prims.of_int (81)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "FStar.InteractiveHelpers.Output.fst"
                                               (Prims.of_int (47))
                                               (Prims.of_int (84))
                                               (Prims.of_int (73))
                                               (Prims.of_int (31)))))
                                      (Obj.magic uu___4)
                                      (fun uu___5 ->
                                         (fun post_subst ->
                                            let uu___5 =
                                              Obj.magic
                                                (FStar_Tactics_Effect.lift_div_tac
                                                   (fun uu___6 ->
                                                      if
                                                        FStar_Pervasives_Native.uu___is_Some
                                                          shadowed_bv
                                                      then
                                                        FStar_Pervasives_Native.fst
                                                          (_split_subst_at_bv
                                                             (FStar_Pervasives_Native.__proj__Some__item__v
                                                                shadowed_bv)
                                                             post_subst)
                                                      else post_subst)) in
                                            Obj.magic
                                              (FStar_Tactics_Effect.tac_bind
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "FStar.InteractiveHelpers.Output.fst"
                                                          (Prims.of_int (54))
                                                          (Prims.of_int (4))
                                                          (Prims.of_int (55))
                                                          (Prims.of_int (19)))))
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "FStar.InteractiveHelpers.Output.fst"
                                                          (Prims.of_int (56))
                                                          (Prims.of_int (4))
                                                          (Prims.of_int (73))
                                                          (Prims.of_int (31)))))
                                                 (Obj.magic uu___5)
                                                 (fun uu___6 ->
                                                    (fun pre_subst ->
                                                       let uu___6 =
                                                         Obj.magic
                                                           (FStar_Tactics_Effect.lift_div_tac
                                                              (fun uu___7 ->
                                                                 fun subst1
                                                                   ->
                                                                   let uu___8
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    fun
                                                                    uu___10
                                                                    ->
                                                                    match uu___10
                                                                    with
                                                                    | 
                                                                    ((x, ty),
                                                                    y) ->
                                                                    let uu___11
                                                                    =
                                                                    let uu___12
                                                                    =
                                                                    FStar_InteractiveHelpers_Base.abv_to_string
                                                                    x in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Output.fst"
                                                                    (Prims.of_int (59))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (59))
                                                                    (Prims.of_int (27)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Output.fst"
                                                                    (Prims.of_int (59))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (59))
                                                                    (Prims.of_int (63)))))
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
                                                                    FStarC_Tactics_V1_Builtins.term_to_string
                                                                    y in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Output.fst"
                                                                    (Prims.of_int (59))
                                                                    (Prims.of_int (39))
                                                                    (Prims.of_int (59))
                                                                    (Prims.of_int (55)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___16)
                                                                    (fun
                                                                    uu___17
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___18
                                                                    ->
                                                                    Prims.strcat
                                                                    uu___17
                                                                    ")\n")) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Output.fst"
                                                                    (Prims.of_int (59))
                                                                    (Prims.of_int (39))
                                                                    (Prims.of_int (59))
                                                                    (Prims.of_int (63)))))
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
                                                                    " -> "
                                                                    uu___16)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Output.fst"
                                                                    (Prims.of_int (59))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (59))
                                                                    (Prims.of_int (63)))))
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
                                                                    uu___13
                                                                    uu___15))))
                                                                    uu___13) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Output.fst"
                                                                    (Prims.of_int (59))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (59))
                                                                    (Prims.of_int (63)))))
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
                                                                    "("
                                                                    uu___12)))) in
                                                                   FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Output.fst"
                                                                    (Prims.of_int (59))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (59))
                                                                    (Prims.of_int (63)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Output.fst"
                                                                    (Prims.of_int (60))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (62))
                                                                    (Prims.of_int (48)))))
                                                                    (Obj.magic
                                                                    uu___8)
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun
                                                                    to_string
                                                                    ->
                                                                    let uu___9
                                                                    =
                                                                    FStar_Tactics_Util.map
                                                                    to_string
                                                                    subst1 in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Output.fst"
                                                                    (Prims.of_int (61))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (61))
                                                                    (Prims.of_int (33)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Output.fst"
                                                                    (Prims.of_int (62))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (62))
                                                                    (Prims.of_int (48)))))
                                                                    (Obj.magic
                                                                    uu___9)
                                                                    (fun str
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    FStar_List_Tot_Base.fold_left
                                                                    (fun x ->
                                                                    fun y ->
                                                                    Prims.strcat
                                                                    x y) ""
                                                                    str))))
                                                                    uu___9))) in
                                                       Obj.magic
                                                         (FStar_Tactics_Effect.tac_bind
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Output.fst"
                                                                    (Prims.of_int (57))
                                                                    (Prims.of_int (42))
                                                                    (Prims.of_int (62))
                                                                    (Prims.of_int (48)))))
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Output.fst"
                                                                    (Prims.of_int (64))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (73))
                                                                    (Prims.of_int (31)))))
                                                            (Obj.magic uu___6)
                                                            (fun uu___7 ->
                                                               (fun
                                                                  subst_to_string
                                                                  ->
                                                                  let uu___7
                                                                    =
                                                                    if dbg
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (let uu___8
                                                                    =
                                                                    let uu___9
                                                                    =
                                                                    let uu___10
                                                                    =
                                                                    subst_to_string
                                                                    pre_subst in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Output.fst"
                                                                    (Prims.of_int (66))
                                                                    (Prims.of_int (38))
                                                                    (Prims.of_int (66))
                                                                    (Prims.of_int (63)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___10)
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    Prims.strcat
                                                                    "- pre_subst:\n"
                                                                    uu___11)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Output.fst"
                                                                    (Prims.of_int (66))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (66))
                                                                    (Prims.of_int (64)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Output.fst"
                                                                    (Prims.of_int (66))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (66))
                                                                    (Prims.of_int (64)))))
                                                                    (Obj.magic
                                                                    uu___9)
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    uu___10))
                                                                    uu___10) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Output.fst"
                                                                    (Prims.of_int (66))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (66))
                                                                    (Prims.of_int (64)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Output.fst"
                                                                    (Prims.of_int (67))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (67))
                                                                    (Prims.of_int (66)))))
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
                                                                    subst_to_string
                                                                    post_subst in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Output.fst"
                                                                    (Prims.of_int (67))
                                                                    (Prims.of_int (39))
                                                                    (Prims.of_int (67))
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
                                                                    uu___11)
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    Prims.strcat
                                                                    "- post_subst:\n"
                                                                    uu___12)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Output.fst"
                                                                    (Prims.of_int (67))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (67))
                                                                    (Prims.of_int (66)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Output.fst"
                                                                    (Prims.of_int (67))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (67))
                                                                    (Prims.of_int (66)))))
                                                                    (Obj.magic
                                                                    uu___10)
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
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
                                                                    (
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Output.fst"
                                                                    (Prims.of_int (64))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (68))
                                                                    (Prims.of_int (7)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Output.fst"
                                                                    (Prims.of_int (68))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (73))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___7)
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun
                                                                    uu___8 ->
                                                                    let uu___9
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    fun s ->
                                                                    FStar_Tactics_Util.map
                                                                    (fun t ->
                                                                    FStar_InteractiveHelpers_Base.apply_subst
                                                                    ge1.FStar_InteractiveHelpers_Base.env
                                                                    t s))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Output.fst"
                                                                    (Prims.of_int (70))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (70))
                                                                    (Prims.of_int (63)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Output.fst"
                                                                    (Prims.of_int (70))
                                                                    (Prims.of_int (66))
                                                                    (Prims.of_int (73))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___9)
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun
                                                                    apply ->
                                                                    let uu___10
                                                                    =
                                                                    apply
                                                                    pre_subst
                                                                    es.FStar_InteractiveHelpers_Propositions.pres in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Output.fst"
                                                                    (Prims.of_int (71))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (71))
                                                                    (Prims.of_int (36)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Output.fst"
                                                                    (Prims.of_int (71))
                                                                    (Prims.of_int (39))
                                                                    (Prims.of_int (73))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___10)
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    (fun pres
                                                                    ->
                                                                    let uu___11
                                                                    =
                                                                    apply
                                                                    post_subst
                                                                    es.FStar_InteractiveHelpers_Propositions.posts in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Output.fst"
                                                                    (Prims.of_int (72))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (72))
                                                                    (Prims.of_int (39)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Output.fst"
                                                                    (Prims.of_int (73))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (73))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___11)
                                                                    (fun
                                                                    posts ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    (ge1,
                                                                    (FStar_InteractiveHelpers_Propositions.mk_assertions
                                                                    pres
                                                                    posts))))))
                                                                    uu___11)))
                                                                    uu___10)))
                                                                    uu___8)))
                                                                 uu___7)))
                                                      uu___6))) uu___5)))
                            uu___3))) uu___1)
let (string_to_printout : Prims.string -> Prims.string -> Prims.string) =
  fun prefix ->
    fun data ->
      Prims.strcat prefix (Prims.strcat ":\n" (Prims.strcat data "\n"))
let (term_to_printout :
  FStar_InteractiveHelpers_Base.genv ->
    Prims.string ->
      FStarC_Reflection_Types.term ->
        (Prims.string, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun ge ->
    fun prefix ->
      fun t ->
        let uu___ = FStar_InteractiveHelpers_ExploreTerm.abs_free_in ge t in
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.InteractiveHelpers.Output.fst"
                   (Prims.of_int (87)) (Prims.of_int (12))
                   (Prims.of_int (87)) (Prims.of_int (28)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.InteractiveHelpers.Output.fst"
                   (Prims.of_int (87)) (Prims.of_int (31))
                   (Prims.of_int (92)) (Prims.of_int (46)))))
          (Obj.magic uu___)
          (fun uu___1 ->
             (fun abs ->
                let uu___1 =
                  Obj.magic
                    (FStar_Tactics_Effect.lift_div_tac
                       (fun uu___2 ->
                          FStar_List_Tot_Base.map
                            (fun uu___3 ->
                               match uu___3 with
                               | (bv, t1) ->
                                   FStar_Reflection_V1_Derived.mk_binder bv
                                     t1) abs)) in
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "FStar.InteractiveHelpers.Output.fst"
                              (Prims.of_int (88)) (Prims.of_int (20))
                              (Prims.of_int (88)) (Prims.of_int (68)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "FStar.InteractiveHelpers.Output.fst"
                              (Prims.of_int (88)) (Prims.of_int (71))
                              (Prims.of_int (92)) (Prims.of_int (46)))))
                     (Obj.magic uu___1)
                     (fun uu___2 ->
                        (fun abs_binders ->
                           let uu___2 =
                             FStar_Tactics_Util.map
                               (fun uu___3 ->
                                  match uu___3 with
                                  | (bv, uu___4) ->
                                      FStarC_Tactics_V1_Builtins.pack
                                        (FStarC_Reflection_V1_Data.Tv_Var bv))
                               abs in
                           Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "FStar.InteractiveHelpers.Output.fst"
                                         (Prims.of_int (89))
                                         (Prims.of_int (18))
                                         (Prims.of_int (89))
                                         (Prims.of_int (59)))))
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "FStar.InteractiveHelpers.Output.fst"
                                         (Prims.of_int (89))
                                         (Prims.of_int (62))
                                         (Prims.of_int (92))
                                         (Prims.of_int (46)))))
                                (Obj.magic uu___2)
                                (fun uu___3 ->
                                   (fun abs_terms ->
                                      let uu___3 =
                                        FStar_Tactics_V1_Derived.mk_abs
                                          abs_binders t in
                                      Obj.magic
                                        (FStar_Tactics_Effect.tac_bind
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "FStar.InteractiveHelpers.Output.fst"
                                                    (Prims.of_int (90))
                                                    (Prims.of_int (10))
                                                    (Prims.of_int (90))
                                                    (Prims.of_int (30)))))
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "FStar.InteractiveHelpers.Output.fst"
                                                    (Prims.of_int (90))
                                                    (Prims.of_int (33))
                                                    (Prims.of_int (92))
                                                    (Prims.of_int (46)))))
                                           (Obj.magic uu___3)
                                           (fun uu___4 ->
                                              (fun t1 ->
                                                 let uu___4 =
                                                   Obj.magic
                                                     (FStar_Tactics_Effect.lift_div_tac
                                                        (fun uu___5 ->
                                                           FStar_Reflection_V1_Derived.mk_e_app
                                                             t1 abs_terms)) in
                                                 Obj.magic
                                                   (FStar_Tactics_Effect.tac_bind
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "FStar.InteractiveHelpers.Output.fst"
                                                               (Prims.of_int (91))
                                                               (Prims.of_int (10))
                                                               (Prims.of_int (91))
                                                               (Prims.of_int (30)))))
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "FStar.InteractiveHelpers.Output.fst"
                                                               (Prims.of_int (92))
                                                               (Prims.of_int (2))
                                                               (Prims.of_int (92))
                                                               (Prims.of_int (46)))))
                                                      (Obj.magic uu___4)
                                                      (fun uu___5 ->
                                                         (fun t2 ->
                                                            let uu___5 =
                                                              FStarC_Tactics_V1_Builtins.term_to_string
                                                                t2 in
                                                            Obj.magic
                                                              (FStar_Tactics_Effect.tac_bind
                                                                 (FStar_Sealed.seal
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Output.fst"
                                                                    (Prims.of_int (92))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (92))
                                                                    (Prims.of_int (46)))))
                                                                 (FStar_Sealed.seal
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Output.fst"
                                                                    (Prims.of_int (92))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (92))
                                                                    (Prims.of_int (46)))))
                                                                 (Obj.magic
                                                                    uu___5)
                                                                 (fun uu___6
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    string_to_printout
                                                                    prefix
                                                                    uu___6))))
                                                           uu___5))) uu___4)))
                                     uu___3))) uu___2))) uu___1)
let (opt_term_to_printout :
  FStar_InteractiveHelpers_Base.genv ->
    Prims.string ->
      FStarC_Reflection_Types.term FStar_Pervasives_Native.option ->
        (Prims.string, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___2 ->
    fun uu___1 ->
      fun uu___ ->
        (fun ge ->
           fun prefix ->
             fun t ->
               match t with
               | FStar_Pervasives_Native.Some t' ->
                   Obj.magic (Obj.repr (term_to_printout ge prefix t'))
               | FStar_Pervasives_Native.None ->
                   Obj.magic
                     (Obj.repr
                        (FStar_Tactics_Effect.lift_div_tac
                           (fun uu___ -> string_to_printout prefix ""))))
          uu___2 uu___1 uu___
let (proposition_to_printout :
  FStar_InteractiveHelpers_Base.genv ->
    Prims.string ->
      FStar_InteractiveHelpers_Propositions.proposition ->
        (Prims.string, unit) FStar_Tactics_Effect.tac_repr)
  = fun ge -> fun prefix -> fun p -> term_to_printout ge prefix p
let (propositions_to_printout :
  FStar_InteractiveHelpers_Base.genv ->
    Prims.string ->
      FStar_InteractiveHelpers_Propositions.proposition Prims.list ->
        (Prims.string, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun ge ->
    fun prefix ->
      fun pl ->
        let uu___ =
          Obj.magic
            (FStar_Tactics_Effect.lift_div_tac
               (fun uu___1 ->
                  fun i ->
                    fun p ->
                      let uu___2 =
                        Obj.magic
                          (FStar_Tactics_Effect.lift_div_tac
                             (fun uu___3 ->
                                Prims.strcat prefix
                                  (Prims.strcat ":prop"
                                     (Prims.string_of_int i)))) in
                      FStar_Tactics_Effect.tac_bind
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "FStar.InteractiveHelpers.Output.fst"
                                 (Prims.of_int (104)) (Prims.of_int (18))
                                 (Prims.of_int (104)) (Prims.of_int (52)))))
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "FStar.InteractiveHelpers.Output.fst"
                                 (Prims.of_int (105)) (Prims.of_int (4))
                                 (Prims.of_int (105)) (Prims.of_int (40)))))
                        (Obj.magic uu___2)
                        (fun uu___3 ->
                           (fun prefix' ->
                              Obj.magic
                                (proposition_to_printout ge prefix' p))
                             uu___3))) in
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.InteractiveHelpers.Output.fst"
                   (Prims.of_int (103)) (Prims.of_int (28))
                   (Prims.of_int (105)) (Prims.of_int (40)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.InteractiveHelpers.Output.fst"
                   (Prims.of_int (106)) (Prims.of_int (4))
                   (Prims.of_int (113)) (Prims.of_int (5)))))
          (Obj.magic uu___)
          (fun uu___1 ->
             (fun prop_to_printout ->
                let uu___1 =
                  Obj.magic
                    (FStar_Tactics_Effect.lift_div_tac
                       (fun uu___2 ->
                          string_to_printout (Prims.strcat prefix ":num")
                            (Prims.string_of_int
                               (FStar_List_Tot_Base.length pl)))) in
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "FStar.InteractiveHelpers.Output.fst"
                              (Prims.of_int (107)) (Prims.of_int (12))
                              (Prims.of_int (107)) (Prims.of_int (85)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "FStar.InteractiveHelpers.Output.fst"
                              (Prims.of_int (107)) (Prims.of_int (88))
                              (Prims.of_int (113)) (Prims.of_int (5)))))
                     (Obj.magic uu___1)
                     (fun uu___2 ->
                        (fun str ->
                           let uu___2 =
                             Obj.magic
                               (FStar_Tactics_Effect.lift_div_tac
                                  (fun uu___3 ->
                                     fun s_i ->
                                       fun p ->
                                         let uu___4 =
                                           Obj.magic
                                             (FStar_Tactics_Effect.lift_div_tac
                                                (fun uu___5 -> s_i)) in
                                         FStar_Tactics_Effect.tac_bind
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "FStar.InteractiveHelpers.Output.fst"
                                                    (Prims.of_int (109))
                                                    (Prims.of_int (15))
                                                    (Prims.of_int (109))
                                                    (Prims.of_int (18)))))
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "FStar.InteractiveHelpers.Output.fst"
                                                    (Prims.of_int (108))
                                                    (Prims.of_int (46))
                                                    (Prims.of_int (110))
                                                    (Prims.of_int (33)))))
                                           (Obj.magic uu___4)
                                           (fun uu___5 ->
                                              (fun uu___5 ->
                                                 match uu___5 with
                                                 | (s, i) ->
                                                     let uu___6 =
                                                       let uu___7 =
                                                         prop_to_printout i p in
                                                       FStar_Tactics_Effect.tac_bind
                                                         (FStar_Sealed.seal
                                                            (Obj.magic
                                                               (FStar_Range.mk_range
                                                                  "FStar.InteractiveHelpers.Output.fst"
                                                                  (Prims.of_int (110))
                                                                  (Prims.of_int (8))
                                                                  (Prims.of_int (110))
                                                                  (Prims.of_int (28)))))
                                                         (FStar_Sealed.seal
                                                            (Obj.magic
                                                               (FStar_Range.mk_range
                                                                  "Prims.fst"
                                                                  (Prims.of_int (611))
                                                                  (Prims.of_int (19))
                                                                  (Prims.of_int (611))
                                                                  (Prims.of_int (31)))))
                                                         (Obj.magic uu___7)
                                                         (fun uu___8 ->
                                                            FStar_Tactics_Effect.lift_div_tac
                                                              (fun uu___9 ->
                                                                 Prims.strcat
                                                                   s uu___8)) in
                                                     Obj.magic
                                                       (FStar_Tactics_Effect.tac_bind
                                                          (FStar_Sealed.seal
                                                             (Obj.magic
                                                                (FStar_Range.mk_range
                                                                   "FStar.InteractiveHelpers.Output.fst"
                                                                   (Prims.of_int (110))
                                                                   (Prims.of_int (4))
                                                                   (Prims.of_int (110))
                                                                   (Prims.of_int (28)))))
                                                          (FStar_Sealed.seal
                                                             (Obj.magic
                                                                (FStar_Range.mk_range
                                                                   "FStar.InteractiveHelpers.Output.fst"
                                                                   (Prims.of_int (110))
                                                                   (Prims.of_int (4))
                                                                   (Prims.of_int (110))
                                                                   (Prims.of_int (33)))))
                                                          (Obj.magic uu___6)
                                                          (fun uu___7 ->
                                                             FStar_Tactics_Effect.lift_div_tac
                                                               (fun uu___8 ->
                                                                  (uu___7,
                                                                    (
                                                                    i +
                                                                    Prims.int_one))))))
                                                uu___5))) in
                           Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "FStar.InteractiveHelpers.Output.fst"
                                         (Prims.of_int (108))
                                         (Prims.of_int (46))
                                         (Prims.of_int (110))
                                         (Prims.of_int (33)))))
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "FStar.InteractiveHelpers.Output.fst"
                                         (Prims.of_int (111))
                                         (Prims.of_int (4))
                                         (Prims.of_int (113))
                                         (Prims.of_int (5)))))
                                (Obj.magic uu___2)
                                (fun uu___3 ->
                                   (fun concat_prop ->
                                      let uu___3 =
                                        FStar_Tactics_Util.fold_left
                                          concat_prop (str, Prims.int_zero)
                                          pl in
                                      Obj.magic
                                        (FStar_Tactics_Effect.tac_bind
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "FStar.InteractiveHelpers.Output.fst"
                                                    (Prims.of_int (112))
                                                    (Prims.of_int (15))
                                                    (Prims.of_int (112))
                                                    (Prims.of_int (47)))))
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "FStar.InteractiveHelpers.Output.fst"
                                                    (Prims.of_int (111))
                                                    (Prims.of_int (4))
                                                    (Prims.of_int (113))
                                                    (Prims.of_int (5)))))
                                           (Obj.magic uu___3)
                                           (fun uu___4 ->
                                              FStar_Tactics_Effect.lift_div_tac
                                                (fun uu___5 ->
                                                   match uu___4 with
                                                   | (str1, uu___6) -> str1))))
                                     uu___3))) uu___2))) uu___1)
let (error_message_to_printout :
  Prims.string -> Prims.string FStar_Pervasives_Native.option -> Prims.string)
  =
  fun prefix ->
    fun message ->
      let msg =
        match message with
        | FStar_Pervasives_Native.Some msg1 -> msg1
        | uu___ -> "" in
      string_to_printout (Prims.strcat prefix ":error") msg
type export_result =
  | ESuccess of FStar_InteractiveHelpers_Base.genv *
  FStar_InteractiveHelpers_Propositions.assertions 
  | EFailure of Prims.string 
let (uu___is_ESuccess : export_result -> Prims.bool) =
  fun projectee ->
    match projectee with | ESuccess (ge, a) -> true | uu___ -> false
let (__proj__ESuccess__item__ge :
  export_result -> FStar_InteractiveHelpers_Base.genv) =
  fun projectee -> match projectee with | ESuccess (ge, a) -> ge
let (__proj__ESuccess__item__a :
  export_result -> FStar_InteractiveHelpers_Propositions.assertions) =
  fun projectee -> match projectee with | ESuccess (ge, a) -> a
let (uu___is_EFailure : export_result -> Prims.bool) =
  fun projectee ->
    match projectee with | EFailure err -> true | uu___ -> false
let (__proj__EFailure__item__err : export_result -> Prims.string) =
  fun projectee -> match projectee with | EFailure err -> err
let (result_to_printout :
  Prims.string ->
    export_result -> (Prims.string, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun prefix ->
    fun res ->
      let uu___ =
        Obj.magic
          (FStar_Tactics_Effect.lift_div_tac
             (fun uu___1 -> Prims.strcat prefix ":BEGIN\n")) in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.InteractiveHelpers.Output.fst"
                 (Prims.of_int (126)) (Prims.of_int (12))
                 (Prims.of_int (126)) (Prims.of_int (31)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.InteractiveHelpers.Output.fst"
                 (Prims.of_int (126)) (Prims.of_int (34))
                 (Prims.of_int (142)) (Prims.of_int (50)))))
        (Obj.magic uu___)
        (fun uu___1 ->
           (fun str ->
              let uu___1 =
                match res with
                | ESuccess (ge, a) ->
                    Obj.magic
                      (Obj.repr
                         (FStar_Tactics_Effect.lift_div_tac
                            (fun uu___2 ->
                               (FStar_Pervasives_Native.None, ge,
                                 (a.FStar_InteractiveHelpers_Propositions.pres),
                                 (a.FStar_InteractiveHelpers_Propositions.posts)))))
                | EFailure err ->
                    Obj.magic
                      (Obj.repr
                         (let uu___2 =
                            let uu___3 =
                              FStarC_Tactics_V1_Builtins.top_env () in
                            FStar_Tactics_Effect.tac_bind
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "FStar.InteractiveHelpers.Output.fst"
                                       (Prims.of_int (134))
                                       (Prims.of_int (28))
                                       (Prims.of_int (134))
                                       (Prims.of_int (40)))))
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "FStar.InteractiveHelpers.Output.fst"
                                       (Prims.of_int (134))
                                       (Prims.of_int (15))
                                       (Prims.of_int (134))
                                       (Prims.of_int (40)))))
                              (Obj.magic uu___3)
                              (fun uu___4 ->
                                 FStar_Tactics_Effect.lift_div_tac
                                   (fun uu___5 ->
                                      FStar_InteractiveHelpers_Base.mk_init_genv
                                        uu___4)) in
                          FStar_Tactics_Effect.tac_bind
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.InteractiveHelpers.Output.fst"
                                     (Prims.of_int (134)) (Prims.of_int (15))
                                     (Prims.of_int (134)) (Prims.of_int (40)))))
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.InteractiveHelpers.Output.fst"
                                     (Prims.of_int (135)) (Prims.of_int (6))
                                     (Prims.of_int (135)) (Prims.of_int (26)))))
                            (Obj.magic uu___2)
                            (fun ge ->
                               FStar_Tactics_Effect.lift_div_tac
                                 (fun uu___3 ->
                                    ((FStar_Pervasives_Native.Some err), ge,
                                      [], []))))) in
              Obj.magic
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range
                            "FStar.InteractiveHelpers.Output.fst"
                            (Prims.of_int (131)) (Prims.of_int (4))
                            (Prims.of_int (135)) (Prims.of_int (26)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range
                            "FStar.InteractiveHelpers.Output.fst"
                            (Prims.of_int (126)) (Prims.of_int (34))
                            (Prims.of_int (142)) (Prims.of_int (50)))))
                   (Obj.magic uu___1)
                   (fun uu___2 ->
                      (fun uu___2 ->
                         match uu___2 with
                         | (err, ge, pres, posts) ->
                             let uu___3 =
                               Obj.magic
                                 (FStar_Tactics_Effect.lift_div_tac
                                    (fun uu___4 ->
                                       Prims.strcat str
                                         (error_message_to_printout prefix
                                            err))) in
                             Obj.magic
                               (FStar_Tactics_Effect.tac_bind
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "FStar.InteractiveHelpers.Output.fst"
                                           (Prims.of_int (138))
                                           (Prims.of_int (12))
                                           (Prims.of_int (138))
                                           (Prims.of_int (54)))))
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "FStar.InteractiveHelpers.Output.fst"
                                           (Prims.of_int (138))
                                           (Prims.of_int (57))
                                           (Prims.of_int (142))
                                           (Prims.of_int (50)))))
                                  (Obj.magic uu___3)
                                  (fun uu___4 ->
                                     (fun str1 ->
                                        let uu___4 =
                                          let uu___5 =
                                            propositions_to_printout ge
                                              (Prims.strcat prefix ":pres")
                                              pres in
                                          FStar_Tactics_Effect.tac_bind
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "FStar.InteractiveHelpers.Output.fst"
                                                     (Prims.of_int (140))
                                                     (Prims.of_int (18))
                                                     (Prims.of_int (140))
                                                     (Prims.of_int (69)))))
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "Prims.fst"
                                                     (Prims.of_int (611))
                                                     (Prims.of_int (19))
                                                     (Prims.of_int (611))
                                                     (Prims.of_int (31)))))
                                            (Obj.magic uu___5)
                                            (fun uu___6 ->
                                               FStar_Tactics_Effect.lift_div_tac
                                                 (fun uu___7 ->
                                                    Prims.strcat str1 uu___6)) in
                                        Obj.magic
                                          (FStar_Tactics_Effect.tac_bind
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "FStar.InteractiveHelpers.Output.fst"
                                                      (Prims.of_int (140))
                                                      (Prims.of_int (12))
                                                      (Prims.of_int (140))
                                                      (Prims.of_int (69)))))
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "FStar.InteractiveHelpers.Output.fst"
                                                      (Prims.of_int (140))
                                                      (Prims.of_int (72))
                                                      (Prims.of_int (142))
                                                      (Prims.of_int (50)))))
                                             (Obj.magic uu___4)
                                             (fun uu___5 ->
                                                (fun str2 ->
                                                   let uu___5 =
                                                     let uu___6 =
                                                       propositions_to_printout
                                                         ge
                                                         (Prims.strcat prefix
                                                            ":posts") posts in
                                                     FStar_Tactics_Effect.tac_bind
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "FStar.InteractiveHelpers.Output.fst"
                                                                (Prims.of_int (141))
                                                                (Prims.of_int (18))
                                                                (Prims.of_int (141))
                                                                (Prims.of_int (71)))))
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
                                                                 str2 uu___7)) in
                                                   Obj.magic
                                                     (FStar_Tactics_Effect.tac_bind
                                                        (FStar_Sealed.seal
                                                           (Obj.magic
                                                              (FStar_Range.mk_range
                                                                 "FStar.InteractiveHelpers.Output.fst"
                                                                 (Prims.of_int (141))
                                                                 (Prims.of_int (12))
                                                                 (Prims.of_int (141))
                                                                 (Prims.of_int (71)))))
                                                        (FStar_Sealed.seal
                                                           (Obj.magic
                                                              (FStar_Range.mk_range
                                                                 "Prims.fst"
                                                                 (Prims.of_int (611))
                                                                 (Prims.of_int (19))
                                                                 (Prims.of_int (611))
                                                                 (Prims.of_int (31)))))
                                                        (Obj.magic uu___5)
                                                        (fun str3 ->
                                                           FStar_Tactics_Effect.lift_div_tac
                                                             (fun uu___6 ->
                                                                Prims.strcat
                                                                  str3
                                                                  (Prims.strcat
                                                                    prefix
                                                                    ":END\n%FIH:FSTAR_META:END%")))))
                                                  uu___5))) uu___4))) uu___2)))
             uu___1)
let (printout_result :
  Prims.string -> export_result -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun prefix ->
    fun res ->
      let uu___ = result_to_printout prefix res in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.InteractiveHelpers.Output.fst"
                 (Prims.of_int (146)) (Prims.of_int (8)) (Prims.of_int (146))
                 (Prims.of_int (39)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.InteractiveHelpers.Output.fst"
                 (Prims.of_int (146)) (Prims.of_int (2)) (Prims.of_int (146))
                 (Prims.of_int (39))))) (Obj.magic uu___)
        (fun uu___1 ->
           (fun uu___1 -> Obj.magic (FStarC_Tactics_V1_Builtins.print uu___1))
             uu___1)
let (printout_success :
  FStar_InteractiveHelpers_Base.genv ->
    FStar_InteractiveHelpers_Propositions.assertions ->
      (unit, unit) FStar_Tactics_Effect.tac_repr)
  = fun ge -> fun a -> printout_result "ainfo" (ESuccess (ge, a))
let (printout_failure :
  FStarC_Errors_Msg.error_message ->
    (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun err ->
    printout_result "ainfo" (EFailure (FStarC_Errors_Msg.rendermsg err))
let (_debug_print_var :
  Prims.string ->
    FStarC_Reflection_Types.term ->
      (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun name ->
    fun t ->
      let uu___ =
        let uu___1 =
          let uu___2 =
            let uu___3 =
              let uu___4 = FStarC_Tactics_V1_Builtins.term_to_string t in
              FStar_Tactics_Effect.tac_bind
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range
                         "FStar.InteractiveHelpers.Output.fst"
                         (Prims.of_int (157)) (Prims.of_int (46))
                         (Prims.of_int (157)) (Prims.of_int (62)))))
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Prims.fst" (Prims.of_int (611))
                         (Prims.of_int (19)) (Prims.of_int (611))
                         (Prims.of_int (31))))) (Obj.magic uu___4)
                (fun uu___5 ->
                   FStar_Tactics_Effect.lift_div_tac
                     (fun uu___6 -> Prims.strcat ": " uu___5)) in
            FStar_Tactics_Effect.tac_bind
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range
                       "FStar.InteractiveHelpers.Output.fst"
                       (Prims.of_int (157)) (Prims.of_int (39))
                       (Prims.of_int (157)) (Prims.of_int (62)))))
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "Prims.fst" (Prims.of_int (611))
                       (Prims.of_int (19)) (Prims.of_int (611))
                       (Prims.of_int (31))))) (Obj.magic uu___3)
              (fun uu___4 ->
                 FStar_Tactics_Effect.lift_div_tac
                   (fun uu___5 -> Prims.strcat name uu___4)) in
          FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "FStar.InteractiveHelpers.Output.fst"
                     (Prims.of_int (157)) (Prims.of_int (32))
                     (Prims.of_int (157)) (Prims.of_int (62)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Prims.fst" (Prims.of_int (611))
                     (Prims.of_int (19)) (Prims.of_int (611))
                     (Prims.of_int (31))))) (Obj.magic uu___2)
            (fun uu___3 ->
               FStar_Tactics_Effect.lift_div_tac
                 (fun uu___4 -> Prims.strcat "_debug_print_var: " uu___3)) in
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.InteractiveHelpers.Output.fst"
                   (Prims.of_int (157)) (Prims.of_int (8))
                   (Prims.of_int (157)) (Prims.of_int (63)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.InteractiveHelpers.Output.fst"
                   (Prims.of_int (157)) (Prims.of_int (2))
                   (Prims.of_int (157)) (Prims.of_int (63)))))
          (Obj.magic uu___1)
          (fun uu___2 ->
             (fun uu___2 ->
                Obj.magic (FStarC_Tactics_V1_Builtins.print uu___2)) uu___2) in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.InteractiveHelpers.Output.fst"
                 (Prims.of_int (157)) (Prims.of_int (2)) (Prims.of_int (157))
                 (Prims.of_int (63)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.InteractiveHelpers.Output.fst"
                 (Prims.of_int (158)) (Prims.of_int (2)) (Prims.of_int (170))
                 (Prims.of_int (33))))) (Obj.magic uu___)
        (fun uu___1 ->
           (fun uu___1 ->
              let uu___2 =
                let uu___3 =
                  let uu___4 = FStarC_Tactics_V1_Builtins.top_env () in
                  FStar_Tactics_Effect.tac_bind
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range
                             "FStar.InteractiveHelpers.Output.fst"
                             (Prims.of_int (158)) (Prims.of_int (22))
                             (Prims.of_int (158)) (Prims.of_int (34)))))
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range
                             "FStar.InteractiveHelpers.Output.fst"
                             (Prims.of_int (158)) (Prims.of_int (14))
                             (Prims.of_int (158)) (Prims.of_int (36)))))
                    (Obj.magic uu___4)
                    (fun uu___5 ->
                       (fun uu___5 ->
                          Obj.magic
                            (FStar_InteractiveHelpers_ExploreTerm.safe_tc
                               uu___5 t)) uu___5) in
                FStar_Tactics_Effect.tac_bind
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range
                           "FStar.InteractiveHelpers.Output.fst"
                           (Prims.of_int (158)) (Prims.of_int (14))
                           (Prims.of_int (158)) (Prims.of_int (36)))))
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range
                           "FStar.InteractiveHelpers.Output.fst"
                           (Prims.of_int (158)) (Prims.of_int (8))
                           (Prims.of_int (160)) (Prims.of_int (11)))))
                  (Obj.magic uu___3)
                  (fun uu___4 ->
                     (fun uu___4 ->
                        match uu___4 with
                        | FStar_Pervasives_Native.Some ty ->
                            Obj.magic
                              (Obj.repr
                                 (let uu___5 =
                                    let uu___6 =
                                      FStarC_Tactics_V1_Builtins.term_to_string
                                        ty in
                                    FStar_Tactics_Effect.tac_bind
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "FStar.InteractiveHelpers.Output.fst"
                                               (Prims.of_int (159))
                                               (Prims.of_int (33))
                                               (Prims.of_int (159))
                                               (Prims.of_int (50)))))
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
                                              Prims.strcat "type: " uu___7)) in
                                  FStar_Tactics_Effect.tac_bind
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "FStar.InteractiveHelpers.Output.fst"
                                             (Prims.of_int (159))
                                             (Prims.of_int (21))
                                             (Prims.of_int (159))
                                             (Prims.of_int (51)))))
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "FStar.InteractiveHelpers.Output.fst"
                                             (Prims.of_int (159))
                                             (Prims.of_int (15))
                                             (Prims.of_int (159))
                                             (Prims.of_int (51)))))
                                    (Obj.magic uu___5)
                                    (fun uu___6 ->
                                       (fun uu___6 ->
                                          Obj.magic
                                            (FStarC_Tactics_V1_Builtins.print
                                               uu___6)) uu___6)))
                        | uu___5 ->
                            Obj.magic
                              (Obj.repr
                                 (FStar_Tactics_Effect.lift_div_tac
                                    (fun uu___6 -> ())))) uu___4) in
              Obj.magic
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range
                            "FStar.InteractiveHelpers.Output.fst"
                            (Prims.of_int (158)) (Prims.of_int (8))
                            (Prims.of_int (160)) (Prims.of_int (11)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range
                            "FStar.InteractiveHelpers.Output.fst"
                            (Prims.of_int (162)) (Prims.of_int (2))
                            (Prims.of_int (170)) (Prims.of_int (33)))))
                   (Obj.magic uu___2)
                   (fun uu___3 ->
                      (fun uu___3 ->
                         let uu___4 =
                           let uu___5 =
                             let uu___6 =
                               FStar_InteractiveHelpers_Base.term_construct t in
                             FStar_Tactics_Effect.tac_bind
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "FStar.InteractiveHelpers.Output.fst"
                                        (Prims.of_int (162))
                                        (Prims.of_int (25))
                                        (Prims.of_int (162))
                                        (Prims.of_int (41)))))
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
                                       Prims.strcat "qualifier: " uu___7)) in
                           FStar_Tactics_Effect.tac_bind
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "FStar.InteractiveHelpers.Output.fst"
                                      (Prims.of_int (162)) (Prims.of_int (8))
                                      (Prims.of_int (162))
                                      (Prims.of_int (42)))))
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "FStar.InteractiveHelpers.Output.fst"
                                      (Prims.of_int (162)) (Prims.of_int (2))
                                      (Prims.of_int (162))
                                      (Prims.of_int (42)))))
                             (Obj.magic uu___5)
                             (fun uu___6 ->
                                (fun uu___6 ->
                                   Obj.magic
                                     (FStarC_Tactics_V1_Builtins.print uu___6))
                                  uu___6) in
                         Obj.magic
                           (FStar_Tactics_Effect.tac_bind
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "FStar.InteractiveHelpers.Output.fst"
                                       (Prims.of_int (162))
                                       (Prims.of_int (2))
                                       (Prims.of_int (162))
                                       (Prims.of_int (42)))))
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "FStar.InteractiveHelpers.Output.fst"
                                       (Prims.of_int (163))
                                       (Prims.of_int (2))
                                       (Prims.of_int (170))
                                       (Prims.of_int (33)))))
                              (Obj.magic uu___4)
                              (fun uu___5 ->
                                 (fun uu___5 ->
                                    let uu___6 =
                                      let uu___7 =
                                        FStarC_Tactics_V1_Builtins.inspect t in
                                      FStar_Tactics_Effect.tac_bind
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "FStar.InteractiveHelpers.Output.fst"
                                                 (Prims.of_int (163))
                                                 (Prims.of_int (14))
                                                 (Prims.of_int (163))
                                                 (Prims.of_int (23)))))
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "FStar.InteractiveHelpers.Output.fst"
                                                 (Prims.of_int (163))
                                                 (Prims.of_int (8))
                                                 (Prims.of_int (168))
                                                 (Prims.of_int (11)))))
                                        (Obj.magic uu___7)
                                        (fun uu___8 ->
                                           (fun uu___8 ->
                                              match uu___8 with
                                              | FStarC_Reflection_V1_Data.Tv_Var
                                                  bv ->
                                                  Obj.magic
                                                    (Obj.repr
                                                       (let uu___9 =
                                                          Obj.magic
                                                            (FStar_Tactics_Effect.lift_div_tac
                                                               (fun uu___10
                                                                  ->
                                                                  FStarC_Reflection_V1_Builtins.inspect_bv
                                                                    bv)) in
                                                        FStar_Tactics_Effect.tac_bind
                                                          (FStar_Sealed.seal
                                                             (Obj.magic
                                                                (FStar_Range.mk_range
                                                                   "FStar.InteractiveHelpers.Output.fst"
                                                                   (Prims.of_int (165))
                                                                   (Prims.of_int (22))
                                                                   (Prims.of_int (165))
                                                                   (Prims.of_int (35)))))
                                                          (FStar_Sealed.seal
                                                             (Obj.magic
                                                                (FStar_Range.mk_range
                                                                   "FStar.InteractiveHelpers.Output.fst"
                                                                   (Prims.of_int (166))
                                                                   (Prims.of_int (4))
                                                                   (Prims.of_int (167))
                                                                   (Prims.of_int (52)))))
                                                          (Obj.magic uu___9)
                                                          (fun uu___10 ->
                                                             (fun b ->
                                                                let uu___10 =
                                                                  let uu___11
                                                                    =
                                                                    let uu___12
                                                                    =
                                                                    FStar_Tactics_V1_Derived.name_of_bv
                                                                    bv in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Output.fst"
                                                                    (Prims.of_int (166))
                                                                    (Prims.of_int (32))
                                                                    (Prims.of_int (166))
                                                                    (Prims.of_int (45)))))
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
                                                                    uu___13
                                                                    (Prims.strcat
                                                                    "; index: "
                                                                    (Prims.string_of_int
                                                                    b.FStarC_Reflection_V1_Data.bv_index)))) in
                                                                  FStar_Tactics_Effect.tac_bind
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Output.fst"
                                                                    (Prims.of_int (166))
                                                                    (Prims.of_int (32))
                                                                    (Prims.of_int (167))
                                                                    (Prims.of_int (51)))))
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (
                                                                    Obj.magic
                                                                    uu___11)
                                                                    (
                                                                    fun
                                                                    uu___12
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    Prims.strcat
                                                                    "Tv_Var: ppname: "
                                                                    uu___12)) in
                                                                Obj.magic
                                                                  (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Output.fst"
                                                                    (Prims.of_int (166))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (167))
                                                                    (Prims.of_int (52)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Output.fst"
                                                                    (Prims.of_int (166))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (167))
                                                                    (Prims.of_int (52)))))
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
                                                                    uu___11)))
                                                               uu___10)))
                                              | uu___9 ->
                                                  Obj.magic
                                                    (Obj.repr
                                                       (FStar_Tactics_Effect.lift_div_tac
                                                          (fun uu___10 -> ()))))
                                             uu___8) in
                                    Obj.magic
                                      (FStar_Tactics_Effect.tac_bind
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "FStar.InteractiveHelpers.Output.fst"
                                                  (Prims.of_int (163))
                                                  (Prims.of_int (8))
                                                  (Prims.of_int (168))
                                                  (Prims.of_int (11)))))
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "FStar.InteractiveHelpers.Output.fst"
                                                  (Prims.of_int (170))
                                                  (Prims.of_int (2))
                                                  (Prims.of_int (170))
                                                  (Prims.of_int (33)))))
                                         (Obj.magic uu___6)
                                         (fun uu___7 ->
                                            (fun uu___7 ->
                                               Obj.magic
                                                 (FStarC_Tactics_V1_Builtins.print
                                                    "end of _debug_print_var"))
                                              uu___7))) uu___5))) uu___3)))
             uu___1)
let magic_witness : 'a . unit -> 'a =
  fun uu___ ->
    failwith
      "Not yet implemented: FStar.InteractiveHelpers.Output.magic_witness"
let (tadmit_no_warning : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___ ->
    FStar_Tactics_V1_Derived.apply
      (FStarC_Reflection_V2_Builtins.pack_ln
         (FStarC_Reflection_V2_Data.Tv_FVar
            (FStarC_Reflection_V2_Builtins.pack_fv
               ["FStar"; "InteractiveHelpers"; "Output"; "magic_witness"])))
let (pp_tac : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    let uu___1 =
      let uu___2 =
        let uu___3 =
          let uu___4 = FStar_Tactics_V1_Derived.cur_goal () in
          FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "FStar.InteractiveHelpers.Output.fst"
                     (Prims.of_int (184)) (Prims.of_int (47))
                     (Prims.of_int (184)) (Prims.of_int (60)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "FStar.InteractiveHelpers.Output.fst"
                     (Prims.of_int (184)) (Prims.of_int (31))
                     (Prims.of_int (184)) (Prims.of_int (61)))))
            (Obj.magic uu___4)
            (fun uu___5 ->
               (fun uu___5 ->
                  Obj.magic
                    (FStarC_Tactics_V1_Builtins.term_to_string uu___5))
                 uu___5) in
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.InteractiveHelpers.Output.fst"
                   (Prims.of_int (184)) (Prims.of_int (31))
                   (Prims.of_int (184)) (Prims.of_int (61)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "Prims.fst" (Prims.of_int (611))
                   (Prims.of_int (19)) (Prims.of_int (611))
                   (Prims.of_int (31))))) (Obj.magic uu___3)
          (fun uu___4 ->
             FStar_Tactics_Effect.lift_div_tac
               (fun uu___5 -> Prims.strcat "post-processing: " uu___4)) in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.InteractiveHelpers.Output.fst"
                 (Prims.of_int (184)) (Prims.of_int (8)) (Prims.of_int (184))
                 (Prims.of_int (62)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.InteractiveHelpers.Output.fst"
                 (Prims.of_int (184)) (Prims.of_int (2)) (Prims.of_int (184))
                 (Prims.of_int (62))))) (Obj.magic uu___2)
        (fun uu___3 ->
           (fun uu___3 -> Obj.magic (FStarC_Tactics_V1_Builtins.print uu___3))
             uu___3) in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.InteractiveHelpers.Output.fst"
               (Prims.of_int (184)) (Prims.of_int (2)) (Prims.of_int (184))
               (Prims.of_int (62)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.InteractiveHelpers.Output.fst"
               (Prims.of_int (185)) (Prims.of_int (2)) (Prims.of_int (186))
               (Prims.of_int (9))))) (Obj.magic uu___1)
      (fun uu___2 ->
         (fun uu___2 ->
            let uu___3 = FStarC_Tactics_V1_Builtins.dump "" in
            Obj.magic
              (FStar_Tactics_Effect.tac_bind
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range
                          "FStar.InteractiveHelpers.Output.fst"
                          (Prims.of_int (185)) (Prims.of_int (2))
                          (Prims.of_int (185)) (Prims.of_int (9)))))
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range
                          "FStar.InteractiveHelpers.Output.fst"
                          (Prims.of_int (186)) (Prims.of_int (2))
                          (Prims.of_int (186)) (Prims.of_int (9)))))
                 (Obj.magic uu___3)
                 (fun uu___4 ->
                    (fun uu___4 ->
                       Obj.magic (FStar_Tactics_V1_Derived.trefl ())) uu___4)))
           uu___2)