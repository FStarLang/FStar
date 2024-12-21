open Prims
type meta_info = unit
let (focus_on_term : meta_info) =
  Obj.magic
    (fun uu___ ->
       failwith
         "Not yet implemented: FStar.InteractiveHelpers.PostProcess.focus_on_term")
let (end_proof : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    FStarC_Tactics_V1_Builtins.tadmit_t
      (FStarC_Reflection_V2_Builtins.pack_ln
         (FStarC_Reflection_V2_Data.Tv_Const FStarC_Reflection_V2_Data.C_Unit))
let (unsquash_equality :
  FStarC_Reflection_Types.term ->
    ((FStarC_Reflection_Types.term * FStarC_Reflection_Types.term)
       FStar_Pervasives_Native.option,
      unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    let uu___ = FStar_Reflection_V1_Formula.term_as_formula t in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.InteractiveHelpers.PostProcess.fst"
               (Prims.of_int (27)) (Prims.of_int (14)) (Prims.of_int (27))
               (Prims.of_int (31)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.InteractiveHelpers.PostProcess.fst"
               (Prims.of_int (27)) (Prims.of_int (8)) (Prims.of_int (29))
               (Prims.of_int (13))))) (Obj.magic uu___)
      (fun uu___1 ->
         FStar_Tactics_Effect.lift_div_tac
           (fun uu___2 ->
              match uu___1 with
              | FStar_Reflection_V1_Formula.Comp
                  (FStar_Reflection_V1_Formula.Eq uu___3, l, r) ->
                  FStar_Pervasives_Native.Some (l, r)
              | uu___3 -> FStar_Pervasives_Native.None))
let (pp_explore :
  Prims.bool ->
    Prims.bool ->
      unit ->
        Obj.t FStar_InteractiveHelpers_ExploreTerm.explorer ->
          Obj.t -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun dbg ->
    fun dfs ->
      fun a ->
        fun f ->
          fun x ->
            let uu___ = FStar_Tactics_V1_Derived.cur_goal () in
            FStar_Tactics_Effect.tac_bind
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range
                       "FStar.InteractiveHelpers.PostProcess.fst"
                       (Prims.of_int (38)) (Prims.of_int (10))
                       (Prims.of_int (38)) (Prims.of_int (21)))))
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range
                       "FStar.InteractiveHelpers.PostProcess.fst"
                       (Prims.of_int (38)) (Prims.of_int (24))
                       (Prims.of_int (49)) (Prims.of_int (5)))))
              (Obj.magic uu___)
              (fun uu___1 ->
                 (fun g ->
                    let uu___1 = FStar_Tactics_V1_Derived.cur_env () in
                    Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "FStar.InteractiveHelpers.PostProcess.fst"
                                  (Prims.of_int (39)) (Prims.of_int (10))
                                  (Prims.of_int (39)) (Prims.of_int (20)))))
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "FStar.InteractiveHelpers.PostProcess.fst"
                                  (Prims.of_int (40)) (Prims.of_int (2))
                                  (Prims.of_int (49)) (Prims.of_int (5)))))
                         (Obj.magic uu___1)
                         (fun uu___2 ->
                            (fun e ->
                               let uu___2 =
                                 let uu___3 =
                                   let uu___4 =
                                     FStarC_Tactics_V1_Builtins.term_to_string
                                       g in
                                   FStar_Tactics_Effect.tac_bind
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "FStar.InteractiveHelpers.PostProcess.fst"
                                              (Prims.of_int (40))
                                              (Prims.of_int (38))
                                              (Prims.of_int (40))
                                              (Prims.of_int (54)))))
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
                                             Prims.strcat "[> pp_explore:\n"
                                               uu___5)) in
                                 FStar_Tactics_Effect.tac_bind
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "FStar.InteractiveHelpers.PostProcess.fst"
                                            (Prims.of_int (40))
                                            (Prims.of_int (16))
                                            (Prims.of_int (40))
                                            (Prims.of_int (55)))))
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "FStar.InteractiveHelpers.PostProcess.fst"
                                            (Prims.of_int (40))
                                            (Prims.of_int (2))
                                            (Prims.of_int (40))
                                            (Prims.of_int (55)))))
                                   (Obj.magic uu___3)
                                   (fun uu___4 ->
                                      (fun uu___4 ->
                                         Obj.magic
                                           (FStar_InteractiveHelpers_Base.print_dbg
                                              dbg uu___4)) uu___4) in
                               Obj.magic
                                 (FStar_Tactics_Effect.tac_bind
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "FStar.InteractiveHelpers.PostProcess.fst"
                                             (Prims.of_int (40))
                                             (Prims.of_int (2))
                                             (Prims.of_int (40))
                                             (Prims.of_int (55)))))
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "FStar.InteractiveHelpers.PostProcess.fst"
                                             (Prims.of_int (41))
                                             (Prims.of_int (8))
                                             (Prims.of_int (48))
                                             (Prims.of_int (52)))))
                                    (Obj.magic uu___2)
                                    (fun uu___3 ->
                                       (fun uu___3 ->
                                          let uu___4 = unsquash_equality g in
                                          Obj.magic
                                            (FStar_Tactics_Effect.tac_bind
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "FStar.InteractiveHelpers.PostProcess.fst"
                                                        (Prims.of_int (41))
                                                        (Prims.of_int (14))
                                                        (Prims.of_int (41))
                                                        (Prims.of_int (33)))))
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "FStar.InteractiveHelpers.PostProcess.fst"
                                                        (Prims.of_int (41))
                                                        (Prims.of_int (8))
                                                        (Prims.of_int (48))
                                                        (Prims.of_int (52)))))
                                               (Obj.magic uu___4)
                                               (fun uu___5 ->
                                                  (fun uu___5 ->
                                                     match uu___5 with
                                                     | FStar_Pervasives_Native.Some
                                                         (l, uu___6) ->
                                                         let uu___7 =
                                                           FStar_InteractiveHelpers_ExploreTerm.safe_typ_or_comp
                                                             dbg e l in
                                                         Obj.magic
                                                           (FStar_Tactics_Effect.tac_bind
                                                              (FStar_Sealed.seal
                                                                 (Obj.magic
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (43))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (43))
                                                                    (Prims.of_int (36)))))
                                                              (FStar_Sealed.seal
                                                                 (Obj.magic
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (43))
                                                                    (Prims.of_int (39))
                                                                    (Prims.of_int (47))
                                                                    (Prims.of_int (16)))))
                                                              (Obj.magic
                                                                 uu___7)
                                                              (fun uu___8 ->
                                                                 (fun c ->
                                                                    let uu___8
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    FStar_InteractiveHelpers_Base.mk_genv
                                                                    e [] [])) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (44))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (44))
                                                                    (Prims.of_int (28)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (45))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (47))
                                                                    (Prims.of_int (16)))))
                                                                    (Obj.magic
                                                                    uu___8)
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun ge
                                                                    ->
                                                                    let uu___9
                                                                    =
                                                                    let uu___10
                                                                    =
                                                                    let uu___11
                                                                    =
                                                                    FStarC_Tactics_V1_Builtins.term_to_string
                                                                    l in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (45))
                                                                    (Prims.of_int (51))
                                                                    (Prims.of_int (45))
                                                                    (Prims.of_int (67)))))
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
                                                                    "[> About to explore term:\n"
                                                                    uu___12)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (45))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (45))
                                                                    (Prims.of_int (68)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (45))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (45))
                                                                    (Prims.of_int (68)))))
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
                                                                    uu___11) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (45))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (45))
                                                                    (Prims.of_int (68)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (45))
                                                                    (Prims.of_int (69))
                                                                    (Prims.of_int (47))
                                                                    (Prims.of_int (16)))))
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
                                                                    FStar_InteractiveHelpers_ExploreTerm.explore_term
                                                                    dbg dfs
                                                                    () f x ge
                                                                    [] c l in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (46))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (46))
                                                                    (Prims.of_int (49)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (47))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (47))
                                                                    (Prims.of_int (16)))))
                                                                    (Obj.magic
                                                                    uu___11)
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    (fun x1
                                                                    ->
                                                                    Obj.magic
                                                                    (end_proof
                                                                    ()))
                                                                    uu___12)))
                                                                    uu___10)))
                                                                    uu___9)))
                                                                   uu___8))
                                                     | uu___6 ->
                                                         Obj.magic
                                                           (FStar_InteractiveHelpers_Base.mfail
                                                              "pp_explore: not a squashed equality"))
                                                    uu___5))) uu___3)))
                              uu___2))) uu___1)
let (pp_explore_print_goal :
  unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    let uu___1 =
      Obj.magic
        (FStar_Tactics_Effect.lift_div_tac
           (fun uu___2 ->
              (fun uu___2 ->
                 fun uu___3 ->
                   fun uu___4 ->
                     fun uu___5 ->
                       fun uu___6 ->
                         fun uu___7 ->
                           Obj.magic
                             (FStar_Tactics_Effect.lift_div_tac
                                (fun uu___8 ->
                                   ((), FStarC_Tactics_Types.Continue))))
                uu___2)) in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.InteractiveHelpers.PostProcess.fst"
               (Prims.of_int (57)) (Prims.of_int (4)) (Prims.of_int (57))
               (Prims.of_int (35)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.InteractiveHelpers.PostProcess.fst"
               (Prims.of_int (59)) (Prims.of_int (2)) (Prims.of_int (59))
               (Prims.of_int (28))))) (Obj.magic uu___1)
      (fun uu___2 ->
         (fun f ->
            Obj.magic (pp_explore true false () (Obj.magic f) (Obj.repr ())))
           uu___2)
let (is_focus_on_term :
  FStarC_Reflection_Types.term ->
    (Prims.bool, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___ ->
    (fun t ->
       Obj.magic
         (FStar_Tactics_Effect.lift_div_tac
            (fun uu___ ->
               FStar_Reflection_V1_Derived.is_fvar t
                 "FStar.InteractiveHelpers.PostProcess.focus_on_term")))
      uu___
let (term_is_assert_or_assume :
  FStarC_Reflection_Types.term ->
    (FStarC_Reflection_Types.term FStar_Pervasives_Native.option, unit)
      FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    let uu___ = FStarC_Tactics_V1_Builtins.inspect t in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.InteractiveHelpers.PostProcess.fst"
               (Prims.of_int (70)) (Prims.of_int (8)) (Prims.of_int (70))
               (Prims.of_int (17)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.InteractiveHelpers.PostProcess.fst"
               (Prims.of_int (70)) (Prims.of_int (2)) (Prims.of_int (75))
               (Prims.of_int (13))))) (Obj.magic uu___)
      (fun uu___1 ->
         FStar_Tactics_Effect.lift_div_tac
           (fun uu___2 ->
              match uu___1 with
              | FStarC_Reflection_V1_Data.Tv_App
                  (hd, (a, FStarC_Reflection_V1_Data.Q_Explicit)) ->
                  if
                    FStar_Reflection_V1_Derived.is_any_fvar a
                      ["Prims._assert";
                      "FStar.Pervasives.assert_norm";
                      "Prims._assume"]
                  then FStar_Pervasives_Native.Some a
                  else FStar_Pervasives_Native.None
              | uu___3 -> FStar_Pervasives_Native.None))
let (is_focused_term :
  FStarC_Reflection_V1_Data.term_view ->
    (FStarC_Reflection_Types.term FStar_Pervasives_Native.option, unit)
      FStar_Tactics_Effect.tac_repr)
  =
  fun uu___ ->
    (fun tv ->
       match tv with
       | FStarC_Reflection_V1_Data.Tv_Let
           (recf, attrs, uu___, uu___1, def, body) ->
           Obj.magic
             (Obj.repr
                (let uu___2 = is_focus_on_term def in
                 FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range
                            "FStar.InteractiveHelpers.PostProcess.fst"
                            (Prims.of_int (83)) (Prims.of_int (7))
                            (Prims.of_int (83)) (Prims.of_int (27)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range
                            "FStar.InteractiveHelpers.PostProcess.fst"
                            (Prims.of_int (83)) (Prims.of_int (4))
                            (Prims.of_int (83)) (Prims.of_int (52)))))
                   (Obj.magic uu___2)
                   (fun uu___3 ->
                      FStar_Tactics_Effect.lift_div_tac
                        (fun uu___4 ->
                           if uu___3
                           then FStar_Pervasives_Native.Some body
                           else FStar_Pervasives_Native.None))))
       | uu___ ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.lift_div_tac
                   (fun uu___1 -> FStar_Pervasives_Native.None)))) uu___
type 'a exploration_result =
  {
  ge: FStar_InteractiveHelpers_Base.genv ;
  parents:
    (FStar_InteractiveHelpers_Base.genv *
      FStarC_Reflection_V1_Data.term_view) Prims.list
    ;
  tgt_comp:
    FStar_InteractiveHelpers_ExploreTerm.typ_or_comp
      FStar_Pervasives_Native.option
    ;
  res: 'a }
let __proj__Mkexploration_result__item__ge :
  'a . 'a exploration_result -> FStar_InteractiveHelpers_Base.genv =
  fun projectee ->
    match projectee with | { ge; parents; tgt_comp; res;_} -> ge
let __proj__Mkexploration_result__item__parents :
  'a .
    'a exploration_result ->
      (FStar_InteractiveHelpers_Base.genv *
        FStarC_Reflection_V1_Data.term_view) Prims.list
  =
  fun projectee ->
    match projectee with | { ge; parents; tgt_comp; res;_} -> parents
let __proj__Mkexploration_result__item__tgt_comp :
  'a .
    'a exploration_result ->
      FStar_InteractiveHelpers_ExploreTerm.typ_or_comp
        FStar_Pervasives_Native.option
  =
  fun projectee ->
    match projectee with | { ge; parents; tgt_comp; res;_} -> tgt_comp
let __proj__Mkexploration_result__item__res :
  'a . 'a exploration_result -> 'a =
  fun projectee ->
    match projectee with | { ge; parents; tgt_comp; res;_} -> res
let mk_exploration_result :
  'uuuuu .
    unit ->
      FStar_InteractiveHelpers_Base.genv ->
        (FStar_InteractiveHelpers_Base.genv *
          FStarC_Reflection_V1_Data.term_view) Prims.list ->
          FStar_InteractiveHelpers_ExploreTerm.typ_or_comp
            FStar_Pervasives_Native.option ->
            'uuuuu -> 'uuuuu exploration_result
  =
  fun uu___ ->
    fun uu___1 ->
      fun uu___2 ->
        fun uu___3 ->
          fun uu___4 ->
            { ge = uu___1; parents = uu___2; tgt_comp = uu___3; res = uu___4
            }
type 'a pred_explorer =
  FStar_InteractiveHelpers_Base.genv ->
    (FStar_InteractiveHelpers_Base.genv *
      FStarC_Reflection_V1_Data.term_view) Prims.list ->
      FStar_InteractiveHelpers_ExploreTerm.typ_or_comp
        FStar_Pervasives_Native.option ->
        FStarC_Reflection_V1_Data.term_view ->
          ('a FStar_Pervasives_Native.option, unit)
            FStar_Tactics_Effect.tac_repr
let find_predicated_term_explorer :
  'a .
    'a pred_explorer ->
      Prims.bool ->
        'a exploration_result FStar_Pervasives_Native.option
          FStar_InteractiveHelpers_ExploreTerm.explorer
  =
  fun pred ->
    fun dbg ->
      fun acc ->
        fun ge ->
          fun pl ->
            fun opt_c ->
              fun t ->
                let uu___ =
                  if FStar_Pervasives_Native.uu___is_Some acc
                  then
                    Obj.magic
                      (Obj.repr
                         (FStar_InteractiveHelpers_Base.mfail
                            "find_focused_term_explorer: non empty accumulator"))
                  else
                    Obj.magic
                      (Obj.repr
                         (FStar_Tactics_Effect.lift_div_tac
                            (fun uu___2 -> ()))) in
                FStar_Tactics_Effect.tac_bind
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range
                           "FStar.InteractiveHelpers.PostProcess.fst"
                           (Prims.of_int (102)) (Prims.of_int (2))
                           (Prims.of_int (102)) (Prims.of_int (77)))))
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range
                           "FStar.InteractiveHelpers.PostProcess.fst"
                           (Prims.of_int (103)) (Prims.of_int (2))
                           (Prims.of_int (109)) (Prims.of_int (26)))))
                  (Obj.magic uu___)
                  (fun uu___1 ->
                     (fun uu___1 ->
                        let uu___2 =
                          if dbg
                          then
                            Obj.magic
                              (Obj.repr
                                 (let uu___3 =
                                    let uu___4 =
                                      let uu___5 =
                                        FStar_InteractiveHelpers_Base.term_view_construct
                                          t in
                                      FStar_Tactics_Effect.tac_bind
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "FStar.InteractiveHelpers.PostProcess.fst"
                                                 (Prims.of_int (105))
                                                 (Prims.of_int (47))
                                                 (Prims.of_int (105))
                                                 (Prims.of_int (68)))))
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "FStar.InteractiveHelpers.PostProcess.fst"
                                                 (Prims.of_int (105))
                                                 (Prims.of_int (47))
                                                 (Prims.of_int (105))
                                                 (Prims.of_int (95)))))
                                        (Obj.magic uu___5)
                                        (fun uu___6 ->
                                           (fun uu___6 ->
                                              let uu___7 =
                                                let uu___8 =
                                                  let uu___9 =
                                                    FStarC_Tactics_V1_Builtins.pack
                                                      t in
                                                  FStar_Tactics_Effect.tac_bind
                                                    (FStar_Sealed.seal
                                                       (Obj.magic
                                                          (FStar_Range.mk_range
                                                             "FStar.InteractiveHelpers.PostProcess.fst"
                                                             (Prims.of_int (101))
                                                             (Prims.of_int (62))
                                                             (Prims.of_int (101))
                                                             (Prims.of_int (63)))))
                                                    (FStar_Sealed.seal
                                                       (Obj.magic
                                                          (FStar_Range.mk_range
                                                             "FStar.InteractiveHelpers.PostProcess.fst"
                                                             (Prims.of_int (105))
                                                             (Prims.of_int (79))
                                                             (Prims.of_int (105))
                                                             (Prims.of_int (95)))))
                                                    (Obj.magic uu___9)
                                                    (fun uu___10 ->
                                                       (fun uu___10 ->
                                                          Obj.magic
                                                            (FStarC_Tactics_V1_Builtins.term_to_string
                                                               uu___10))
                                                         uu___10) in
                                                FStar_Tactics_Effect.tac_bind
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "FStar.InteractiveHelpers.PostProcess.fst"
                                                           (Prims.of_int (105))
                                                           (Prims.of_int (79))
                                                           (Prims.of_int (105))
                                                           (Prims.of_int (95)))))
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
                                                          Prims.strcat ":\n"
                                                            uu___9)) in
                                              Obj.magic
                                                (FStar_Tactics_Effect.tac_bind
                                                   (FStar_Sealed.seal
                                                      (Obj.magic
                                                         (FStar_Range.mk_range
                                                            "FStar.InteractiveHelpers.PostProcess.fst"
                                                            (Prims.of_int (105))
                                                            (Prims.of_int (71))
                                                            (Prims.of_int (105))
                                                            (Prims.of_int (95)))))
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
                                                             uu___6 uu___8))))
                                             uu___6) in
                                    FStar_Tactics_Effect.tac_bind
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "FStar.InteractiveHelpers.PostProcess.fst"
                                               (Prims.of_int (105))
                                               (Prims.of_int (47))
                                               (Prims.of_int (105))
                                               (Prims.of_int (95)))))
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
                                              Prims.strcat
                                                "[> find_focused_term_explorer: "
                                                uu___5)) in
                                  FStar_Tactics_Effect.tac_bind
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "FStar.InteractiveHelpers.PostProcess.fst"
                                             (Prims.of_int (105))
                                             (Prims.of_int (10))
                                             (Prims.of_int (105))
                                             (Prims.of_int (96)))))
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "FStar.InteractiveHelpers.PostProcess.fst"
                                             (Prims.of_int (105))
                                             (Prims.of_int (4))
                                             (Prims.of_int (105))
                                             (Prims.of_int (96)))))
                                    (Obj.magic uu___3)
                                    (fun uu___4 ->
                                       (fun uu___4 ->
                                          Obj.magic
                                            (FStarC_Tactics_V1_Builtins.print
                                               uu___4)) uu___4)))
                          else
                            Obj.magic
                              (Obj.repr
                                 (FStar_Tactics_Effect.lift_div_tac
                                    (fun uu___4 -> ()))) in
                        Obj.magic
                          (FStar_Tactics_Effect.tac_bind
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "FStar.InteractiveHelpers.PostProcess.fst"
                                      (Prims.of_int (103)) (Prims.of_int (2))
                                      (Prims.of_int (106)) (Prims.of_int (7)))))
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "FStar.InteractiveHelpers.PostProcess.fst"
                                      (Prims.of_int (107)) (Prims.of_int (2))
                                      (Prims.of_int (109))
                                      (Prims.of_int (26)))))
                             (Obj.magic uu___2)
                             (fun uu___3 ->
                                (fun uu___3 ->
                                   let uu___4 = pred ge pl opt_c t in
                                   Obj.magic
                                     (FStar_Tactics_Effect.tac_bind
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "FStar.InteractiveHelpers.PostProcess.fst"
                                                 (Prims.of_int (107))
                                                 (Prims.of_int (8))
                                                 (Prims.of_int (107))
                                                 (Prims.of_int (26)))))
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "FStar.InteractiveHelpers.PostProcess.fst"
                                                 (Prims.of_int (107))
                                                 (Prims.of_int (2))
                                                 (Prims.of_int (109))
                                                 (Prims.of_int (26)))))
                                        (Obj.magic uu___4)
                                        (fun uu___5 ->
                                           FStar_Tactics_Effect.lift_div_tac
                                             (fun uu___6 ->
                                                match uu___5 with
                                                | FStar_Pervasives_Native.Some
                                                    ft ->
                                                    ((FStar_Pervasives_Native.Some
                                                        ((mk_exploration_result
                                                            ()) ge pl opt_c
                                                           ft)),
                                                      FStarC_Tactics_Types.Abort)
                                                | FStar_Pervasives_Native.None
                                                    ->
                                                    (FStar_Pervasives_Native.None,
                                                      FStarC_Tactics_Types.Continue)))))
                                  uu___3))) uu___1)
let find_predicated_term :
  'a .
    'a pred_explorer ->
      Prims.bool ->
        Prims.bool ->
          FStar_InteractiveHelpers_Base.genv ->
            (FStar_InteractiveHelpers_Base.genv *
              FStarC_Reflection_V1_Data.term_view) Prims.list ->
              FStar_InteractiveHelpers_ExploreTerm.typ_or_comp
                FStar_Pervasives_Native.option ->
                FStarC_Reflection_Types.term ->
                  ('a exploration_result FStar_Pervasives_Native.option,
                    unit) FStar_Tactics_Effect.tac_repr
  =
  fun pred ->
    fun dbg ->
      fun dfs ->
        fun ge ->
          fun pl ->
            fun opt_c ->
              fun t ->
                let uu___ =
                  Obj.magic
                    (FStar_InteractiveHelpers_ExploreTerm.explore_term dbg
                       dfs ()
                       (Obj.magic (find_predicated_term_explorer pred dbg))
                       (Obj.magic FStar_Pervasives_Native.None) ge pl opt_c t) in
                FStar_Tactics_Effect.tac_bind
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range
                           "FStar.InteractiveHelpers.PostProcess.fst"
                           (Prims.of_int (116)) (Prims.of_int (6))
                           (Prims.of_int (118)) (Prims.of_int (39)))))
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range
                           "FStar.InteractiveHelpers.PostProcess.fst"
                           (Prims.of_int (116)) (Prims.of_int (2))
                           (Prims.of_int (118)) (Prims.of_int (39)))))
                  (Obj.magic uu___)
                  (fun uu___1 ->
                     FStar_Tactics_Effect.lift_div_tac
                       (fun uu___2 -> FStar_Pervasives_Native.fst uu___1))
let (_is_focused_term_explorer : FStarC_Reflection_Types.term pred_explorer)
  = fun ge -> fun pl -> fun opt_c -> fun tv -> is_focused_term tv
let (find_focused_term :
  Prims.bool ->
    Prims.bool ->
      FStar_InteractiveHelpers_Base.genv ->
        (FStar_InteractiveHelpers_Base.genv *
          FStarC_Reflection_V1_Data.term_view) Prims.list ->
          FStar_InteractiveHelpers_ExploreTerm.typ_or_comp
            FStar_Pervasives_Native.option ->
            FStarC_Reflection_Types.term ->
              (FStarC_Reflection_Types.term exploration_result
                 FStar_Pervasives_Native.option,
                unit) FStar_Tactics_Effect.tac_repr)
  =
  fun dbg ->
    fun dfs ->
      fun ge ->
        fun pl ->
          fun opt_c ->
            fun t ->
              find_predicated_term _is_focused_term_explorer dbg dfs ge pl
                opt_c t
let (find_focused_term_in_current_goal :
  Prims.bool ->
    (FStarC_Reflection_Types.term exploration_result, unit)
      FStar_Tactics_Effect.tac_repr)
  =
  fun dbg ->
    let uu___ = FStar_Tactics_V1_Derived.cur_goal () in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.InteractiveHelpers.PostProcess.fst"
               (Prims.of_int (132)) (Prims.of_int (10)) (Prims.of_int (132))
               (Prims.of_int (21)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.InteractiveHelpers.PostProcess.fst"
               (Prims.of_int (132)) (Prims.of_int (24)) (Prims.of_int (149))
               (Prims.of_int (5))))) (Obj.magic uu___)
      (fun uu___1 ->
         (fun g ->
            let uu___1 = FStar_Tactics_V1_Derived.cur_env () in
            Obj.magic
              (FStar_Tactics_Effect.tac_bind
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range
                          "FStar.InteractiveHelpers.PostProcess.fst"
                          (Prims.of_int (133)) (Prims.of_int (10))
                          (Prims.of_int (133)) (Prims.of_int (20)))))
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range
                          "FStar.InteractiveHelpers.PostProcess.fst"
                          (Prims.of_int (134)) (Prims.of_int (2))
                          (Prims.of_int (149)) (Prims.of_int (5)))))
                 (Obj.magic uu___1)
                 (fun uu___2 ->
                    (fun e ->
                       let uu___2 =
                         let uu___3 =
                           let uu___4 =
                             FStarC_Tactics_V1_Builtins.term_to_string g in
                           FStar_Tactics_Effect.tac_bind
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "FStar.InteractiveHelpers.PostProcess.fst"
                                      (Prims.of_int (134))
                                      (Prims.of_int (63))
                                      (Prims.of_int (134))
                                      (Prims.of_int (79)))))
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
                                     Prims.strcat
                                       "[> find_focused_assert_in_current_goal:\n"
                                       uu___5)) in
                         FStar_Tactics_Effect.tac_bind
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                    (Prims.of_int (134)) (Prims.of_int (16))
                                    (Prims.of_int (134)) (Prims.of_int (80)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                    (Prims.of_int (134)) (Prims.of_int (2))
                                    (Prims.of_int (134)) (Prims.of_int (80)))))
                           (Obj.magic uu___3)
                           (fun uu___4 ->
                              (fun uu___4 ->
                                 Obj.magic
                                   (FStar_InteractiveHelpers_Base.print_dbg
                                      dbg uu___4)) uu___4) in
                       Obj.magic
                         (FStar_Tactics_Effect.tac_bind
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.InteractiveHelpers.PostProcess.fst"
                                     (Prims.of_int (134)) (Prims.of_int (2))
                                     (Prims.of_int (134)) (Prims.of_int (80)))))
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.InteractiveHelpers.PostProcess.fst"
                                     (Prims.of_int (135)) (Prims.of_int (8))
                                     (Prims.of_int (148)) (Prims.of_int (75)))))
                            (Obj.magic uu___2)
                            (fun uu___3 ->
                               (fun uu___3 ->
                                  let uu___4 = unsquash_equality g in
                                  Obj.magic
                                    (FStar_Tactics_Effect.tac_bind
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "FStar.InteractiveHelpers.PostProcess.fst"
                                                (Prims.of_int (135))
                                                (Prims.of_int (14))
                                                (Prims.of_int (135))
                                                (Prims.of_int (33)))))
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "FStar.InteractiveHelpers.PostProcess.fst"
                                                (Prims.of_int (135))
                                                (Prims.of_int (8))
                                                (Prims.of_int (148))
                                                (Prims.of_int (75)))))
                                       (Obj.magic uu___4)
                                       (fun uu___5 ->
                                          (fun uu___5 ->
                                             match uu___5 with
                                             | FStar_Pervasives_Native.Some
                                                 (l, uu___6) ->
                                                 let uu___7 =
                                                   FStar_InteractiveHelpers_ExploreTerm.safe_typ_or_comp
                                                     dbg e l in
                                                 Obj.magic
                                                   (FStar_Tactics_Effect.tac_bind
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "FStar.InteractiveHelpers.PostProcess.fst"
                                                               (Prims.of_int (137))
                                                               (Prims.of_int (12))
                                                               (Prims.of_int (137))
                                                               (Prims.of_int (36)))))
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "FStar.InteractiveHelpers.PostProcess.fst"
                                                               (Prims.of_int (137))
                                                               (Prims.of_int (39))
                                                               (Prims.of_int (147))
                                                               (Prims.of_int (7)))))
                                                      (Obj.magic uu___7)
                                                      (fun uu___8 ->
                                                         (fun c ->
                                                            let uu___8 =
                                                              Obj.magic
                                                                (FStar_Tactics_Effect.lift_div_tac
                                                                   (fun
                                                                    uu___9 ->
                                                                    FStar_InteractiveHelpers_Base.mk_genv
                                                                    e [] [])) in
                                                            Obj.magic
                                                              (FStar_Tactics_Effect.tac_bind
                                                                 (FStar_Sealed.seal
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (138))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (138))
                                                                    (Prims.of_int (28)))))
                                                                 (FStar_Sealed.seal
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (139))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (147))
                                                                    (Prims.of_int (7)))))
                                                                 (Obj.magic
                                                                    uu___8)
                                                                 (fun uu___9
                                                                    ->
                                                                    (fun ge
                                                                    ->
                                                                    let uu___9
                                                                    =
                                                                    let uu___10
                                                                    =
                                                                    let uu___11
                                                                    =
                                                                    FStarC_Tactics_V1_Builtins.term_to_string
                                                                    l in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (139))
                                                                    (Prims.of_int (51))
                                                                    (Prims.of_int (139))
                                                                    (Prims.of_int (67)))))
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
                                                                    "[> About to explore term:\n"
                                                                    uu___12)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (139))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (139))
                                                                    (Prims.of_int (68)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (139))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (139))
                                                                    (Prims.of_int (68)))))
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
                                                                    uu___11) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (139))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (139))
                                                                    (Prims.of_int (68)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (140))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (146))
                                                                    (Prims.of_int (32)))))
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
                                                                    find_focused_term
                                                                    dbg true
                                                                    ge [] c l in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (140))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (140))
                                                                    (Prims.of_int (52)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (140))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (146))
                                                                    (Prims.of_int (32)))))
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
                                                                    FStar_Pervasives_Native.Some
                                                                    res ->
                                                                    let uu___13
                                                                    =
                                                                    let uu___14
                                                                    =
                                                                    let uu___15
                                                                    =
                                                                    FStarC_Tactics_V1_Builtins.term_to_string
                                                                    res.res in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (142))
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (142))
                                                                    (Prims.of_int (72)))))
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
                                                                    "[> Found focused term:\n"
                                                                    uu___16)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (142))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (142))
                                                                    (Prims.of_int (73)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (142))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (142))
                                                                    (Prims.of_int (73)))))
                                                                    (Obj.magic
                                                                    uu___14)
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    uu___15))
                                                                    uu___15) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (142))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (142))
                                                                    (Prims.of_int (73)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (141))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (141))
                                                                    (Prims.of_int (14)))))
                                                                    (Obj.magic
                                                                    uu___13)
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___15
                                                                    -> res)))
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    let uu___13
                                                                    =
                                                                    let uu___14
                                                                    =
                                                                    FStarC_Tactics_V1_Builtins.term_to_string
                                                                    g in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (146))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (146))
                                                                    (Prims.of_int (31)))))
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
                                                                    "find_focused_term_in_current_goal: could not find a focused term in the current goal: "
                                                                    uu___15)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (145))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (146))
                                                                    (Prims.of_int (32)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (145))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (146))
                                                                    (Prims.of_int (32)))))
                                                                    (Obj.magic
                                                                    uu___13)
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.mfail
                                                                    uu___14))
                                                                    uu___14)))
                                                                    uu___12)))
                                                                    uu___10)))
                                                                    uu___9)))
                                                           uu___8))
                                             | uu___6 ->
                                                 Obj.magic
                                                   (FStar_InteractiveHelpers_Base.mfail
                                                      "find_focused_term_in_current_goal: not a squashed equality"))
                                            uu___5))) uu___3))) uu___2)))
           uu___1)
let (find_focused_assert_in_current_goal :
  Prims.bool ->
    (FStarC_Reflection_Types.term exploration_result, unit)
      FStar_Tactics_Effect.tac_repr)
  =
  fun dbg ->
    let uu___ =
      FStar_InteractiveHelpers_Base.print_dbg dbg
        "[> find_focused_assert_in_current_goal" in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.InteractiveHelpers.PostProcess.fst"
               (Prims.of_int (154)) (Prims.of_int (2)) (Prims.of_int (154))
               (Prims.of_int (58)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.InteractiveHelpers.PostProcess.fst"
               (Prims.of_int (154)) (Prims.of_int (59)) (Prims.of_int (168))
               (Prims.of_int (5))))) (Obj.magic uu___)
      (fun uu___1 ->
         (fun uu___1 ->
            let uu___2 = find_focused_term_in_current_goal dbg in
            Obj.magic
              (FStar_Tactics_Effect.tac_bind
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range
                          "FStar.InteractiveHelpers.PostProcess.fst"
                          (Prims.of_int (155)) (Prims.of_int (12))
                          (Prims.of_int (155)) (Prims.of_int (49)))))
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range
                          "FStar.InteractiveHelpers.PostProcess.fst"
                          (Prims.of_int (156)) (Prims.of_int (2))
                          (Prims.of_int (168)) (Prims.of_int (5)))))
                 (Obj.magic uu___2)
                 (fun uu___3 ->
                    (fun res ->
                       let uu___3 =
                         let uu___4 =
                           let uu___5 =
                             FStarC_Tactics_V1_Builtins.term_to_string
                               res.res in
                           FStar_Tactics_Effect.tac_bind
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "FStar.InteractiveHelpers.PostProcess.fst"
                                      (Prims.of_int (156))
                                      (Prims.of_int (46))
                                      (Prims.of_int (156))
                                      (Prims.of_int (68)))))
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
                                  (fun uu___7 ->
                                     Prims.strcat "[> Found focused term:\n"
                                       uu___6)) in
                         FStar_Tactics_Effect.tac_bind
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                    (Prims.of_int (156)) (Prims.of_int (16))
                                    (Prims.of_int (156)) (Prims.of_int (69)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                    (Prims.of_int (156)) (Prims.of_int (2))
                                    (Prims.of_int (156)) (Prims.of_int (69)))))
                           (Obj.magic uu___4)
                           (fun uu___5 ->
                              (fun uu___5 ->
                                 Obj.magic
                                   (FStar_InteractiveHelpers_Base.print_dbg
                                      dbg uu___5)) uu___5) in
                       Obj.magic
                         (FStar_Tactics_Effect.tac_bind
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.InteractiveHelpers.PostProcess.fst"
                                     (Prims.of_int (156)) (Prims.of_int (2))
                                     (Prims.of_int (156)) (Prims.of_int (69)))))
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.InteractiveHelpers.PostProcess.fst"
                                     (Prims.of_int (156)) (Prims.of_int (70))
                                     (Prims.of_int (168)) (Prims.of_int (5)))))
                            (Obj.magic uu___3)
                            (fun uu___4 ->
                               (fun uu___4 ->
                                  let uu___5 =
                                    let uu___6 =
                                      FStarC_Tactics_V1_Builtins.inspect
                                        res.res in
                                    FStar_Tactics_Effect.tac_bind
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "FStar.InteractiveHelpers.PostProcess.fst"
                                               (Prims.of_int (159))
                                               (Prims.of_int (10))
                                               (Prims.of_int (159))
                                               (Prims.of_int (25)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "FStar.InteractiveHelpers.PostProcess.fst"
                                               (Prims.of_int (159))
                                               (Prims.of_int (4))
                                               (Prims.of_int (163))
                                               (Prims.of_int (14)))))
                                      (Obj.magic uu___6)
                                      (fun uu___7 ->
                                         (fun uu___7 ->
                                            match uu___7 with
                                            | FStarC_Reflection_V1_Data.Tv_Let
                                                (uu___8, uu___9, bv0, ty,
                                                 fterm, uu___10)
                                                ->
                                                Obj.magic
                                                  (Obj.repr
                                                     (let uu___11 =
                                                        FStar_InteractiveHelpers_Base.genv_push_bv
                                                          res.ge bv0 ty false
                                                          FStar_Pervasives_Native.None in
                                                      FStar_Tactics_Effect.tac_bind
                                                        (FStar_Sealed.seal
                                                           (Obj.magic
                                                              (FStar_Range.mk_range
                                                                 "FStar.InteractiveHelpers.PostProcess.fst"
                                                                 (Prims.of_int (161))
                                                                 (Prims.of_int (16))
                                                                 (Prims.of_int (161))
                                                                 (Prims.of_int (53)))))
                                                        (FStar_Sealed.seal
                                                           (Obj.magic
                                                              (FStar_Range.mk_range
                                                                 "FStar.InteractiveHelpers.PostProcess.fst"
                                                                 (Prims.of_int (162))
                                                                 (Prims.of_int (6))
                                                                 (Prims.of_int (162))
                                                                 (Prims.of_int (42)))))
                                                        (Obj.magic uu___11)
                                                        (fun ge' ->
                                                           FStar_Tactics_Effect.lift_div_tac
                                                             (fun uu___12 ->
                                                                {
                                                                  ge = ge';
                                                                  parents =
                                                                    (
                                                                    res.parents);
                                                                  tgt_comp =
                                                                    (
                                                                    res.tgt_comp);
                                                                  res = fterm
                                                                }))))
                                            | uu___8 ->
                                                Obj.magic
                                                  (Obj.repr
                                                     (FStar_Tactics_Effect.lift_div_tac
                                                        (fun uu___9 -> res))))
                                           uu___7) in
                                  Obj.magic
                                    (FStar_Tactics_Effect.tac_bind
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "FStar.InteractiveHelpers.PostProcess.fst"
                                                (Prims.of_int (159))
                                                (Prims.of_int (4))
                                                (Prims.of_int (163))
                                                (Prims.of_int (14)))))
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "FStar.InteractiveHelpers.PostProcess.fst"
                                                (Prims.of_int (165))
                                                (Prims.of_int (8))
                                                (Prims.of_int (167))
                                                (Prims.of_int (38)))))
                                       (Obj.magic uu___5)
                                       (fun uu___6 ->
                                          (fun res' ->
                                             let uu___6 =
                                               term_is_assert_or_assume
                                                 res'.res in
                                             Obj.magic
                                               (FStar_Tactics_Effect.tac_bind
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "FStar.InteractiveHelpers.PostProcess.fst"
                                                           (Prims.of_int (165))
                                                           (Prims.of_int (14))
                                                           (Prims.of_int (165))
                                                           (Prims.of_int (47)))))
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "FStar.InteractiveHelpers.PostProcess.fst"
                                                           (Prims.of_int (165))
                                                           (Prims.of_int (8))
                                                           (Prims.of_int (167))
                                                           (Prims.of_int (38)))))
                                                  (Obj.magic uu___6)
                                                  (fun uu___7 ->
                                                     (fun uu___7 ->
                                                        match uu___7 with
                                                        | FStar_Pervasives_Native.None
                                                            ->
                                                            Obj.magic
                                                              (Obj.repr
                                                                 (let uu___8
                                                                    =
                                                                    let uu___9
                                                                    =
                                                                    FStarC_Tactics_V1_Builtins.term_to_string
                                                                    res.res in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (166))
                                                                    (Prims.of_int (121))
                                                                    (Prims.of_int (166))
                                                                    (Prims.of_int (143)))))
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
                                                                    "find_focused_assert_in_current_goal: the found focused term is not an assertion or an assumption:"
                                                                    uu___10)) in
                                                                  FStar_Tactics_Effect.tac_bind
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (166))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (166))
                                                                    (Prims.of_int (144)))))
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (166))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (166))
                                                                    (Prims.of_int (144)))))
                                                                    (
                                                                    Obj.magic
                                                                    uu___8)
                                                                    (
                                                                    fun
                                                                    uu___9 ->
                                                                    (fun
                                                                    uu___9 ->
                                                                    Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.mfail
                                                                    uu___9))
                                                                    uu___9)))
                                                        | FStar_Pervasives_Native.Some
                                                            tm ->
                                                            Obj.magic
                                                              (Obj.repr
                                                                 (FStar_Tactics_Effect.lift_div_tac
                                                                    (
                                                                    fun
                                                                    uu___8 ->
                                                                    {
                                                                    ge =
                                                                    (res'.ge);
                                                                    parents =
                                                                    (res'.parents);
                                                                    tgt_comp
                                                                    =
                                                                    (res'.tgt_comp);
                                                                    res = tm
                                                                    }))))
                                                       uu___7))) uu___6)))
                                 uu___4))) uu___3))) uu___1)
let (analyze_effectful_term :
  Prims.bool ->
    Prims.bool ->
      Prims.bool ->
        FStarC_Reflection_Types.term exploration_result ->
          (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun dbg ->
    fun with_gpre ->
      fun with_gpost ->
        fun res ->
          let uu___ =
            Obj.magic
              (FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> res.ge)) in
          FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range
                     "FStar.InteractiveHelpers.PostProcess.fst"
                     (Prims.of_int (184)) (Prims.of_int (11))
                     (Prims.of_int (184)) (Prims.of_int (17)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range
                     "FStar.InteractiveHelpers.PostProcess.fst"
                     (Prims.of_int (184)) (Prims.of_int (20))
                     (Prims.of_int (241)) (Prims.of_int (30)))))
            (Obj.magic uu___)
            (fun uu___1 ->
               (fun ge ->
                  let uu___1 =
                    Obj.magic
                      (FStar_Tactics_Effect.lift_div_tac
                         (fun uu___2 -> res.tgt_comp)) in
                  Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "FStar.InteractiveHelpers.PostProcess.fst"
                                (Prims.of_int (185)) (Prims.of_int (14))
                                (Prims.of_int (185)) (Prims.of_int (26)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "FStar.InteractiveHelpers.PostProcess.fst"
                                (Prims.of_int (185)) (Prims.of_int (29))
                                (Prims.of_int (241)) (Prims.of_int (30)))))
                       (Obj.magic uu___1)
                       (fun uu___2 ->
                          (fun opt_c ->
                             let uu___2 =
                               let uu___3 =
                                 FStarC_Tactics_V1_Builtins.inspect res.res in
                               FStar_Tactics_Effect.tac_bind
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "FStar.InteractiveHelpers.PostProcess.fst"
                                          (Prims.of_int (188))
                                          (Prims.of_int (16))
                                          (Prims.of_int (188))
                                          (Prims.of_int (31)))))
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "FStar.InteractiveHelpers.PostProcess.fst"
                                          (Prims.of_int (188))
                                          (Prims.of_int (10))
                                          (Prims.of_int (215))
                                          (Prims.of_int (82)))))
                                 (Obj.magic uu___3)
                                 (fun uu___4 ->
                                    (fun uu___4 ->
                                       match uu___4 with
                                       | FStarC_Reflection_V1_Data.Tv_Let
                                           (uu___5, uu___6, bv0, ty, fterm,
                                            uu___7)
                                           ->
                                           let uu___8 =
                                             let uu___9 =
                                               let uu___10 =
                                                 FStarC_Tactics_V1_Builtins.term_to_string
                                                   fterm in
                                               FStar_Tactics_Effect.tac_bind
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "FStar.InteractiveHelpers.PostProcess.fst"
                                                          (Prims.of_int (195))
                                                          (Prims.of_int (42))
                                                          (Prims.of_int (195))
                                                          (Prims.of_int (62)))))
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
                                                           "Restraining to: "
                                                           uu___11)) in
                                             FStar_Tactics_Effect.tac_bind
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "FStar.InteractiveHelpers.PostProcess.fst"
                                                        (Prims.of_int (195))
                                                        (Prims.of_int (20))
                                                        (Prims.of_int (195))
                                                        (Prims.of_int (63)))))
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "FStar.InteractiveHelpers.PostProcess.fst"
                                                        (Prims.of_int (195))
                                                        (Prims.of_int (6))
                                                        (Prims.of_int (195))
                                                        (Prims.of_int (63)))))
                                               (Obj.magic uu___9)
                                               (fun uu___10 ->
                                                  (fun uu___10 ->
                                                     Obj.magic
                                                       (FStar_InteractiveHelpers_Base.print_dbg
                                                          dbg uu___10))
                                                    uu___10) in
                                           Obj.magic
                                             (FStar_Tactics_Effect.tac_bind
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "FStar.InteractiveHelpers.PostProcess.fst"
                                                         (Prims.of_int (195))
                                                         (Prims.of_int (6))
                                                         (Prims.of_int (195))
                                                         (Prims.of_int (63)))))
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "FStar.InteractiveHelpers.PostProcess.fst"
                                                         (Prims.of_int (195))
                                                         (Prims.of_int (64))
                                                         (Prims.of_int (214))
                                                         (Prims.of_int (69)))))
                                                (Obj.magic uu___8)
                                                (fun uu___9 ->
                                                   (fun uu___9 ->
                                                      let uu___10 =
                                                        let uu___11 =
                                                          let uu___12 =
                                                            FStar_Tactics_V1_Derived.name_of_bv
                                                              bv0 in
                                                          FStar_Tactics_Effect.tac_bind
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (197))
                                                                    (Prims.of_int (36))
                                                                    (Prims.of_int (197))
                                                                    (Prims.of_int (52)))))
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (197))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (197))
                                                                    (Prims.of_int (52)))))
                                                            (Obj.magic
                                                               uu___12)
                                                            (fun uu___13 ->
                                                               (fun uu___13
                                                                  ->
                                                                  Obj.magic
                                                                    (
                                                                    FStar_InteractiveHelpers_Base.genv_get_from_name
                                                                    ge
                                                                    uu___13))
                                                                 uu___13) in
                                                        FStar_Tactics_Effect.tac_bind
                                                          (FStar_Sealed.seal
                                                             (Obj.magic
                                                                (FStar_Range.mk_range
                                                                   "FStar.InteractiveHelpers.PostProcess.fst"
                                                                   (Prims.of_int (197))
                                                                   (Prims.of_int (14))
                                                                   (Prims.of_int (197))
                                                                   (Prims.of_int (52)))))
                                                          (FStar_Sealed.seal
                                                             (Obj.magic
                                                                (FStar_Range.mk_range
                                                                   "FStar.InteractiveHelpers.PostProcess.fst"
                                                                   (Prims.of_int (197))
                                                                   (Prims.of_int (8))
                                                                   (Prims.of_int (199))
                                                                   (Prims.of_int (41)))))
                                                          (Obj.magic uu___11)
                                                          (fun uu___12 ->
                                                             FStar_Tactics_Effect.lift_div_tac
                                                               (fun uu___13
                                                                  ->
                                                                  match uu___12
                                                                  with
                                                                  | FStar_Pervasives_Native.None
                                                                    ->
                                                                    FStar_Pervasives_Native.None
                                                                  | FStar_Pervasives_Native.Some
                                                                    (sbv,
                                                                    uu___14)
                                                                    ->
                                                                    FStar_Pervasives_Native.Some
                                                                    (FStar_Pervasives_Native.fst
                                                                    sbv))) in
                                                      Obj.magic
                                                        (FStar_Tactics_Effect.tac_bind
                                                           (FStar_Sealed.seal
                                                              (Obj.magic
                                                                 (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (197))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (199))
                                                                    (Prims.of_int (41)))))
                                                           (FStar_Sealed.seal
                                                              (Obj.magic
                                                                 (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (200))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (214))
                                                                    (Prims.of_int (69)))))
                                                           (Obj.magic uu___10)
                                                           (fun uu___11 ->
                                                              (fun
                                                                 shadowed_bv
                                                                 ->
                                                                 let uu___11
                                                                   =
                                                                   FStar_InteractiveHelpers_Base.genv_push_bv
                                                                    ge bv0 ty
                                                                    false
                                                                    FStar_Pervasives_Native.None in
                                                                 Obj.magic
                                                                   (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (201))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (201))
                                                                    (Prims.of_int (49)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (201))
                                                                    (Prims.of_int (52))
                                                                    (Prims.of_int (214))
                                                                    (Prims.of_int (69)))))
                                                                    (Obj.magic
                                                                    uu___11)
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    (fun ge1
                                                                    ->
                                                                    let uu___12
                                                                    =
                                                                    let uu___13
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    FStarC_Reflection_V1_Builtins.inspect_bv
                                                                    bv0)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (207))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (207))
                                                                    (Prims.of_int (33)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (207))
                                                                    (Prims.of_int (36))
                                                                    (Prims.of_int (211))
                                                                    (Prims.of_int (21)))))
                                                                    (Obj.magic
                                                                    uu___13)
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    (fun bvv0
                                                                    ->
                                                                    let uu___14
                                                                    =
                                                                    let uu___15
                                                                    =
                                                                    let uu___16
                                                                    =
                                                                    FStar_InteractiveHelpers_Base.abv_to_string
                                                                    bv0 in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (208))
                                                                    (Prims.of_int (59))
                                                                    (Prims.of_int (208))
                                                                    (Prims.of_int (76)))))
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
                                                                    "Variable bound in let: "
                                                                    uu___17)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (208))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (208))
                                                                    (Prims.of_int (77)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (208))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (208))
                                                                    (Prims.of_int (77)))))
                                                                    (Obj.magic
                                                                    uu___15)
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    uu___16))
                                                                    uu___16) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (208))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (208))
                                                                    (Prims.of_int (77)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (209))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (211))
                                                                    (Prims.of_int (21)))))
                                                                    (Obj.magic
                                                                    uu___14)
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    let uu___16
                                                                    =
                                                                    let uu___17
                                                                    =
                                                                    FStarC_Tactics_Unseal.unseal
                                                                    bvv0.FStarC_Reflection_V1_Data.bv_ppname in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (209))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (209))
                                                                    (Prims.of_int (32)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (209))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (209))
                                                                    (Prims.of_int (42)))))
                                                                    (Obj.magic
                                                                    uu___17)
                                                                    (fun
                                                                    uu___18
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___19
                                                                    ->
                                                                    uu___18 =
                                                                    "uu___")) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (209))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (209))
                                                                    (Prims.of_int (42)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (209))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (211))
                                                                    (Prims.of_int (21)))))
                                                                    (Obj.magic
                                                                    uu___16)
                                                                    (fun
                                                                    uu___17
                                                                    ->
                                                                    (fun
                                                                    uu___17
                                                                    ->
                                                                    if
                                                                    uu___17
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_InteractiveHelpers_Base.genv_push_fresh_bv
                                                                    ge1 "ret"
                                                                    ty))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___19
                                                                    ->
                                                                    (ge1,
                                                                    bv0)))))
                                                                    uu___17)))
                                                                    uu___15)))
                                                                    uu___14) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (206))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (211))
                                                                    (Prims.of_int (21)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (201))
                                                                    (Prims.of_int (52))
                                                                    (Prims.of_int (214))
                                                                    (Prims.of_int (69)))))
                                                                    (Obj.magic
                                                                    uu___12)
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    match uu___13
                                                                    with
                                                                    | 
                                                                    (ge2,
                                                                    bv1) ->
                                                                    let uu___14
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___15
                                                                    -> bv1)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (212))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (214))
                                                                    (Prims.of_int (69)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (212))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (214))
                                                                    (Prims.of_int (69)))))
                                                                    (Obj.magic
                                                                    uu___14)
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    (fun bv11
                                                                    ->
                                                                    let uu___15
                                                                    =
                                                                    FStar_InteractiveHelpers_Effectful.compute_eterm_info
                                                                    dbg
                                                                    ge2.FStar_InteractiveHelpers_Base.env
                                                                    fterm in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (213))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (213))
                                                                    (Prims.of_int (53)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (214))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (214))
                                                                    (Prims.of_int (69)))))
                                                                    (Obj.magic
                                                                    uu___15)
                                                                    (fun info
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    (ge2,
                                                                    fterm,
                                                                    info,
                                                                    (FStar_Pervasives_Native.Some
                                                                    bv11),
                                                                    shadowed_bv,
                                                                    true)))))
                                                                    uu___15)))
                                                                    uu___13)))
                                                                    uu___12)))
                                                                uu___11)))
                                                     uu___9))
                                       | uu___5 ->
                                           let uu___6 =
                                             FStar_InteractiveHelpers_Effectful.compute_eterm_info
                                               dbg
                                               ge.FStar_InteractiveHelpers_Base.env
                                               res.res in
                                           Obj.magic
                                             (FStar_Tactics_Effect.tac_bind
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "FStar.InteractiveHelpers.PostProcess.fst"
                                                         (Prims.of_int (215))
                                                         (Prims.of_int (25))
                                                         (Prims.of_int (215))
                                                         (Prims.of_int (62)))))
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "FStar.InteractiveHelpers.PostProcess.fst"
                                                         (Prims.of_int (215))
                                                         (Prims.of_int (11))
                                                         (Prims.of_int (215))
                                                         (Prims.of_int (82)))))
                                                (Obj.magic uu___6)
                                                (fun uu___7 ->
                                                   FStar_Tactics_Effect.lift_div_tac
                                                     (fun uu___8 ->
                                                        (ge, (res.res),
                                                          uu___7,
                                                          FStar_Pervasives_Native.None,
                                                          FStar_Pervasives_Native.None,
                                                          false))))) uu___4) in
                             Obj.magic
                               (FStar_Tactics_Effect.tac_bind
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "FStar.InteractiveHelpers.PostProcess.fst"
                                           (Prims.of_int (188))
                                           (Prims.of_int (10))
                                           (Prims.of_int (215))
                                           (Prims.of_int (82)))))
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "FStar.InteractiveHelpers.PostProcess.fst"
                                           (Prims.of_int (185))
                                           (Prims.of_int (29))
                                           (Prims.of_int (241))
                                           (Prims.of_int (30)))))
                                  (Obj.magic uu___2)
                                  (fun uu___3 ->
                                     (fun uu___3 ->
                                        match uu___3 with
                                        | (ge1, studied_term, info, ret_bv,
                                           shadowed_bv, is_let) ->
                                            let uu___4 =
                                              let uu___5 =
                                                let uu___6 =
                                                  FStar_InteractiveHelpers_Base.term_construct
                                                    studied_term in
                                                FStar_Tactics_Effect.tac_bind
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "FStar.InteractiveHelpers.PostProcess.fst"
                                                           (Prims.of_int (218))
                                                           (Prims.of_int (51))
                                                           (Prims.of_int (218))
                                                           (Prims.of_int (78)))))
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
                                                            "[> Focused term constructor: "
                                                            uu___7)) in
                                              FStar_Tactics_Effect.tac_bind
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "FStar.InteractiveHelpers.PostProcess.fst"
                                                         (Prims.of_int (218))
                                                         (Prims.of_int (16))
                                                         (Prims.of_int (218))
                                                         (Prims.of_int (79)))))
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "FStar.InteractiveHelpers.PostProcess.fst"
                                                         (Prims.of_int (218))
                                                         (Prims.of_int (2))
                                                         (Prims.of_int (218))
                                                         (Prims.of_int (79)))))
                                                (Obj.magic uu___5)
                                                (fun uu___6 ->
                                                   (fun uu___6 ->
                                                      Obj.magic
                                                        (FStar_InteractiveHelpers_Base.print_dbg
                                                           dbg uu___6))
                                                     uu___6) in
                                            Obj.magic
                                              (FStar_Tactics_Effect.tac_bind
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "FStar.InteractiveHelpers.PostProcess.fst"
                                                          (Prims.of_int (218))
                                                          (Prims.of_int (2))
                                                          (Prims.of_int (218))
                                                          (Prims.of_int (79)))))
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "FStar.InteractiveHelpers.PostProcess.fst"
                                                          (Prims.of_int (219))
                                                          (Prims.of_int (2))
                                                          (Prims.of_int (241))
                                                          (Prims.of_int (30)))))
                                                 (Obj.magic uu___4)
                                                 (fun uu___5 ->
                                                    (fun uu___5 ->
                                                       let uu___6 =
                                                         let uu___7 =
                                                           let uu___8 =
                                                             FStar_InteractiveHelpers_Base.genv_to_string
                                                               ge1 in
                                                           FStar_Tactics_Effect.tac_bind
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (219))
                                                                    (Prims.of_int (75))
                                                                    (Prims.of_int (219))
                                                                    (Prims.of_int (93)))))
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                             (Obj.magic
                                                                uu___8)
                                                             (fun uu___9 ->
                                                                FStar_Tactics_Effect.lift_div_tac
                                                                  (fun
                                                                    uu___10
                                                                    ->
                                                                    Prims.strcat
                                                                    "[> Environment information (after effect analysis):\n"
                                                                    uu___9)) in
                                                         FStar_Tactics_Effect.tac_bind
                                                           (FStar_Sealed.seal
                                                              (Obj.magic
                                                                 (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (219))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (219))
                                                                    (Prims.of_int (94)))))
                                                           (FStar_Sealed.seal
                                                              (Obj.magic
                                                                 (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (219))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (219))
                                                                    (Prims.of_int (94)))))
                                                           (Obj.magic uu___7)
                                                           (fun uu___8 ->
                                                              (fun uu___8 ->
                                                                 Obj.magic
                                                                   (FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    uu___8))
                                                                uu___8) in
                                                       Obj.magic
                                                         (FStar_Tactics_Effect.tac_bind
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (219))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (219))
                                                                    (Prims.of_int (94)))))
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (219))
                                                                    (Prims.of_int (95))
                                                                    (Prims.of_int (241))
                                                                    (Prims.of_int (30)))))
                                                            (Obj.magic uu___6)
                                                            (fun uu___7 ->
                                                               (fun uu___7 ->
                                                                  let uu___8
                                                                    =
                                                                    let uu___9
                                                                    =
                                                                    term_is_assert_or_assume
                                                                    studied_term in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (223))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (223))
                                                                    (Prims.of_int (63)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (223))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (223))
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
                                                                    FStar_Pervasives_Native.uu___is_Some
                                                                    uu___10)) in
                                                                  Obj.magic
                                                                    (
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (223))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (223))
                                                                    (Prims.of_int (63)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (223))
                                                                    (Prims.of_int (66))
                                                                    (Prims.of_int (241))
                                                                    (Prims.of_int (30)))))
                                                                    (Obj.magic
                                                                    uu___8)
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun
                                                                    is_assert
                                                                    ->
                                                                    let uu___9
                                                                    =
                                                                    FStar_InteractiveHelpers_Base.opt_tapply
                                                                    (fun x ->
                                                                    FStarC_Tactics_V1_Builtins.pack
                                                                    (FStarC_Reflection_V1_Data.Tv_Var
                                                                    x))
                                                                    ret_bv in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (226))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (226))
                                                                    (Prims.of_int (60)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (226))
                                                                    (Prims.of_int (63))
                                                                    (Prims.of_int (241))
                                                                    (Prims.of_int (30)))))
                                                                    (Obj.magic
                                                                    uu___9)
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun
                                                                    ret_arg
                                                                    ->
                                                                    let uu___10
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    FStar_List_Tot_Base.map
                                                                    FStar_Pervasives_Native.snd
                                                                    res.parents)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (227))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (227))
                                                                    (Prims.of_int (44)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (227))
                                                                    (Prims.of_int (47))
                                                                    (Prims.of_int (241))
                                                                    (Prims.of_int (30)))))
                                                                    (Obj.magic
                                                                    uu___10)
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    (fun
                                                                    parents
                                                                    ->
                                                                    let uu___11
                                                                    =
                                                                    FStar_InteractiveHelpers_Effectful.eterm_info_to_assertions
                                                                    dbg
                                                                    with_gpre
                                                                    with_gpost
                                                                    ge1
                                                                    studied_term
                                                                    is_let
                                                                    is_assert
                                                                    info
                                                                    ret_arg
                                                                    opt_c
                                                                    parents
                                                                    [] in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (229))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (230))
                                                                    (Prims.of_int (68)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (227))
                                                                    (Prims.of_int (47))
                                                                    (Prims.of_int (241))
                                                                    (Prims.of_int (30)))))
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
                                                                    (ge2,
                                                                    asserts)
                                                                    ->
                                                                    let uu___13
                                                                    =
                                                                    FStar_InteractiveHelpers_Propositions.simp_filter_assertions
                                                                    ge2.FStar_InteractiveHelpers_Base.env
                                                                    FStar_InteractiveHelpers_Propositions.simpl_norm_steps
                                                                    asserts in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (232))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (232))
                                                                    (Prims.of_int (71)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (232))
                                                                    (Prims.of_int (74))
                                                                    (Prims.of_int (241))
                                                                    (Prims.of_int (30)))))
                                                                    (Obj.magic
                                                                    uu___13)
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    (fun
                                                                    asserts1
                                                                    ->
                                                                    let uu___14
                                                                    =
                                                                    FStar_InteractiveHelpers_Output.subst_shadowed_with_abs_in_assertions
                                                                    dbg ge2
                                                                    shadowed_bv
                                                                    asserts1 in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (234))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (234))
                                                                    (Prims.of_int (86)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (232))
                                                                    (Prims.of_int (74))
                                                                    (Prims.of_int (241))
                                                                    (Prims.of_int (30)))))
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
                                                                    (ge3,
                                                                    asserts2)
                                                                    ->
                                                                    let uu___16
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___17
                                                                    ->
                                                                    if is_let
                                                                    then
                                                                    asserts2
                                                                    else
                                                                    FStar_InteractiveHelpers_Propositions.mk_assertions
                                                                    (FStar_List_Tot_Base.append
                                                                    asserts2.FStar_InteractiveHelpers_Propositions.pres
                                                                    asserts2.FStar_InteractiveHelpers_Propositions.posts)
                                                                    [])) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (237))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (238))
                                                                    (Prims.of_int (70)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (241))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (241))
                                                                    (Prims.of_int (30)))))
                                                                    (Obj.magic
                                                                    uu___16)
                                                                    (fun
                                                                    uu___17
                                                                    ->
                                                                    (fun
                                                                    asserts3
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_InteractiveHelpers_Output.printout_success
                                                                    ge3
                                                                    asserts3))
                                                                    uu___17)))
                                                                    uu___15)))
                                                                    uu___14)))
                                                                    uu___12)))
                                                                    uu___11)))
                                                                    uu___10)))
                                                                    uu___9)))
                                                                 uu___7)))
                                                      uu___5))) uu___3)))
                            uu___2))) uu___1)
let (pp_analyze_effectful_term :
  Prims.bool ->
    Prims.bool ->
      Prims.bool -> unit -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun dbg ->
    fun with_gpre ->
      fun with_gpost ->
        fun uu___ ->
          FStar_Tactics_V1_Derived.try_with
            (fun uu___1 ->
               match () with
               | () ->
                   let uu___2 = find_focused_term_in_current_goal dbg in
                   FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "FStar.InteractiveHelpers.PostProcess.fst"
                              (Prims.of_int (247)) (Prims.of_int (14))
                              (Prims.of_int (247)) (Prims.of_int (51)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "FStar.InteractiveHelpers.PostProcess.fst"
                              (Prims.of_int (248)) (Prims.of_int (4))
                              (Prims.of_int (249)) (Prims.of_int (16)))))
                     (Obj.magic uu___2)
                     (fun uu___3 ->
                        (fun res ->
                           let uu___3 =
                             analyze_effectful_term dbg with_gpre with_gpost
                               res in
                           Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "FStar.InteractiveHelpers.PostProcess.fst"
                                         (Prims.of_int (248))
                                         (Prims.of_int (4))
                                         (Prims.of_int (248))
                                         (Prims.of_int (55)))))
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "FStar.InteractiveHelpers.PostProcess.fst"
                                         (Prims.of_int (249))
                                         (Prims.of_int (4))
                                         (Prims.of_int (249))
                                         (Prims.of_int (16)))))
                                (Obj.magic uu___3)
                                (fun uu___4 ->
                                   (fun uu___4 -> Obj.magic (end_proof ()))
                                     uu___4))) uu___3))
            (fun uu___1 ->
               (fun uu___1 ->
                  match uu___1 with
                  | FStar_InteractiveHelpers_Base.MetaAnalysis msg ->
                      Obj.magic
                        (Obj.repr
                           (let uu___2 =
                              FStar_InteractiveHelpers_Output.printout_failure
                                msg in
                            FStar_Tactics_Effect.tac_bind
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "FStar.InteractiveHelpers.PostProcess.fst"
                                       (Prims.of_int (250))
                                       (Prims.of_int (29))
                                       (Prims.of_int (250))
                                       (Prims.of_int (49)))))
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "FStar.InteractiveHelpers.PostProcess.fst"
                                       (Prims.of_int (250))
                                       (Prims.of_int (51))
                                       (Prims.of_int (250))
                                       (Prims.of_int (63)))))
                              (Obj.magic uu___2)
                              (fun uu___3 ->
                                 (fun uu___3 -> Obj.magic (end_proof ()))
                                   uu___3)))
                  | err ->
                      Obj.magic (Obj.repr (FStar_Tactics_Effect.raise err)))
                 uu___1)
let _ =
  FStarC_Tactics_Native.register_tactic
    "FStar.InteractiveHelpers.PostProcess.pp_analyze_effectful_term"
    (Prims.of_int (5))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             FStarC_Tactics_InterpFuns.mk_tactic_interpretation_4
               "FStar.InteractiveHelpers.PostProcess.pp_analyze_effectful_term (plugin)"
               (FStarC_Tactics_Native.from_tactic_4 pp_analyze_effectful_term)
               FStarC_Syntax_Embeddings.e_bool
               FStarC_Syntax_Embeddings.e_bool
               FStarC_Syntax_Embeddings.e_bool
               FStarC_Syntax_Embeddings.e_unit
               FStarC_Syntax_Embeddings.e_unit psc ncb us args)
let (remove_b2t :
  FStarC_Reflection_Types.term ->
    (FStarC_Reflection_Types.term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    let uu___ = FStarC_Tactics_V1_Builtins.inspect t in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.InteractiveHelpers.PostProcess.fst"
               (Prims.of_int (266)) (Prims.of_int (8)) (Prims.of_int (266))
               (Prims.of_int (17)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.InteractiveHelpers.PostProcess.fst"
               (Prims.of_int (266)) (Prims.of_int (2)) (Prims.of_int (273))
               (Prims.of_int (10))))) (Obj.magic uu___)
      (fun uu___1 ->
         (fun uu___1 ->
            match uu___1 with
            | FStarC_Reflection_V1_Data.Tv_App
                (hd, (a, FStarC_Reflection_V1_Data.Q_Explicit)) ->
                Obj.magic
                  (Obj.repr
                     (let uu___2 = FStarC_Tactics_V1_Builtins.inspect hd in
                      FStar_Tactics_Effect.tac_bind
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "FStar.InteractiveHelpers.PostProcess.fst"
                                 (Prims.of_int (268)) (Prims.of_int (16))
                                 (Prims.of_int (268)) (Prims.of_int (26)))))
                        (FStar_Sealed.seal
                           (Obj.magic
                              (FStar_Range.mk_range
                                 "FStar.InteractiveHelpers.PostProcess.fst"
                                 (Prims.of_int (268)) (Prims.of_int (10))
                                 (Prims.of_int (271)) (Prims.of_int (12)))))
                        (Obj.magic uu___2)
                        (fun uu___3 ->
                           FStar_Tactics_Effect.lift_div_tac
                             (fun uu___4 ->
                                match uu___3 with
                                | FStarC_Reflection_V1_Data.Tv_FVar fv ->
                                    if
                                      FStar_InteractiveHelpers_Base.fv_eq_name
                                        fv FStar_Reflection_Const.b2t_qn
                                    then a
                                    else t
                                | uu___5 -> t))))
            | uu___2 ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.lift_div_tac (fun uu___3 -> t))))
           uu___1)
let (is_conjunction :
  FStarC_Reflection_Types.term ->
    ((FStarC_Reflection_Types.term * FStarC_Reflection_Types.term)
       FStar_Pervasives_Native.option,
      unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    let uu___ = remove_b2t t in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.InteractiveHelpers.PostProcess.fst"
               (Prims.of_int (279)) (Prims.of_int (10)) (Prims.of_int (279))
               (Prims.of_int (22)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.InteractiveHelpers.PostProcess.fst"
               (Prims.of_int (279)) (Prims.of_int (25)) (Prims.of_int (290))
               (Prims.of_int (13))))) (Obj.magic uu___)
      (fun uu___1 ->
         (fun t1 ->
            let uu___1 = FStar_Tactics_V1_SyntaxHelpers.collect_app t1 in
            Obj.magic
              (FStar_Tactics_Effect.tac_bind
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range
                          "FStar.InteractiveHelpers.PostProcess.fst"
                          (Prims.of_int (280)) (Prims.of_int (19))
                          (Prims.of_int (280)) (Prims.of_int (32)))))
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range
                          "FStar.InteractiveHelpers.PostProcess.fst"
                          (Prims.of_int (279)) (Prims.of_int (25))
                          (Prims.of_int (290)) (Prims.of_int (13)))))
                 (Obj.magic uu___1)
                 (fun uu___2 ->
                    (fun uu___2 ->
                       match uu___2 with
                       | (hd, params) ->
                           (match params with
                            | (x, FStarC_Reflection_V1_Data.Q_Explicit)::
                                (y, FStarC_Reflection_V1_Data.Q_Explicit)::[]
                                ->
                                Obj.magic
                                  (Obj.repr
                                     (let uu___3 =
                                        FStarC_Tactics_V1_Builtins.inspect hd in
                                      FStar_Tactics_Effect.tac_bind
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "FStar.InteractiveHelpers.PostProcess.fst"
                                                 (Prims.of_int (283))
                                                 (Prims.of_int (16))
                                                 (Prims.of_int (283))
                                                 (Prims.of_int (26)))))
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "FStar.InteractiveHelpers.PostProcess.fst"
                                                 (Prims.of_int (283))
                                                 (Prims.of_int (10))
                                                 (Prims.of_int (288))
                                                 (Prims.of_int (15)))))
                                        (Obj.magic uu___3)
                                        (fun uu___4 ->
                                           FStar_Tactics_Effect.lift_div_tac
                                             (fun uu___5 ->
                                                match uu___4 with
                                                | FStarC_Reflection_V1_Data.Tv_FVar
                                                    fv ->
                                                    if
                                                      ((FStarC_Reflection_V1_Builtins.inspect_fv
                                                          fv)
                                                         =
                                                         FStar_Reflection_Const.and_qn)
                                                        ||
                                                        ((FStarC_Reflection_V1_Builtins.inspect_fv
                                                            fv)
                                                           =
                                                           ["Prims";
                                                           "op_AmpAmp"])
                                                    then
                                                      FStar_Pervasives_Native.Some
                                                        (x, y)
                                                    else
                                                      FStar_Pervasives_Native.None
                                                | uu___6 ->
                                                    FStar_Pervasives_Native.None))))
                            | uu___3 ->
                                Obj.magic
                                  (Obj.repr
                                     (FStar_Tactics_Effect.lift_div_tac
                                        (fun uu___4 ->
                                           FStar_Pervasives_Native.None)))))
                      uu___2))) uu___1)
let rec (_split_conjunctions :
  FStarC_Reflection_Types.term Prims.list ->
    FStarC_Reflection_Types.term ->
      (FStarC_Reflection_Types.term Prims.list, unit)
        FStar_Tactics_Effect.tac_repr)
  =
  fun ls ->
    fun t ->
      let uu___ = is_conjunction t in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range
                 "FStar.InteractiveHelpers.PostProcess.fst"
                 (Prims.of_int (295)) (Prims.of_int (8)) (Prims.of_int (295))
                 (Prims.of_int (24)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range
                 "FStar.InteractiveHelpers.PostProcess.fst"
                 (Prims.of_int (295)) (Prims.of_int (2)) (Prims.of_int (300))
                 (Prims.of_int (7))))) (Obj.magic uu___)
        (fun uu___1 ->
           (fun uu___1 ->
              match uu___1 with
              | FStar_Pervasives_Native.None ->
                  Obj.magic
                    (Obj.repr
                       (FStar_Tactics_Effect.lift_div_tac
                          (fun uu___2 -> t :: ls)))
              | FStar_Pervasives_Native.Some (l, r) ->
                  Obj.magic
                    (Obj.repr
                       (let uu___2 = _split_conjunctions ls r in
                        FStar_Tactics_Effect.tac_bind
                          (FStar_Sealed.seal
                             (Obj.magic
                                (FStar_Range.mk_range
                                   "FStar.InteractiveHelpers.PostProcess.fst"
                                   (Prims.of_int (298)) (Prims.of_int (14))
                                   (Prims.of_int (298)) (Prims.of_int (38)))))
                          (FStar_Sealed.seal
                             (Obj.magic
                                (FStar_Range.mk_range
                                   "FStar.InteractiveHelpers.PostProcess.fst"
                                   (Prims.of_int (298)) (Prims.of_int (41))
                                   (Prims.of_int (300)) (Prims.of_int (7)))))
                          (Obj.magic uu___2)
                          (fun uu___3 ->
                             (fun ls1 ->
                                let uu___3 = _split_conjunctions ls1 l in
                                Obj.magic
                                  (FStar_Tactics_Effect.tac_bind
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "FStar.InteractiveHelpers.PostProcess.fst"
                                              (Prims.of_int (299))
                                              (Prims.of_int (14))
                                              (Prims.of_int (299))
                                              (Prims.of_int (39)))))
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "FStar.InteractiveHelpers.PostProcess.fst"
                                              (Prims.of_int (299))
                                              (Prims.of_int (8))
                                              (Prims.of_int (299))
                                              (Prims.of_int (11)))))
                                     (Obj.magic uu___3)
                                     (fun ls2 ->
                                        FStar_Tactics_Effect.lift_div_tac
                                          (fun uu___4 -> ls2)))) uu___3))))
             uu___1)
let (split_conjunctions :
  FStarC_Reflection_Types.term ->
    (FStarC_Reflection_Types.term Prims.list, unit)
      FStar_Tactics_Effect.tac_repr)
  = fun t -> _split_conjunctions [] t
let (split_conjunctions_under_match :
  Prims.bool ->
    FStarC_Reflection_Types.term ->
      (FStarC_Reflection_Types.term Prims.list, unit)
        FStar_Tactics_Effect.tac_repr)
  =
  fun dbg ->
    fun t ->
      let uu___ = remove_b2t t in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range
                 "FStar.InteractiveHelpers.PostProcess.fst"
                 (Prims.of_int (314)) (Prims.of_int (11))
                 (Prims.of_int (314)) (Prims.of_int (23)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range
                 "FStar.InteractiveHelpers.PostProcess.fst"
                 (Prims.of_int (315)) (Prims.of_int (2)) (Prims.of_int (322))
                 (Prims.of_int (7))))) (Obj.magic uu___)
        (fun uu___1 ->
           (fun t1 ->
              let uu___1 =
                let uu___2 =
                  let uu___3 =
                    FStar_InteractiveHelpers_Base.term_construct t1 in
                  FStar_Tactics_Effect.tac_bind
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range
                             "FStar.InteractiveHelpers.PostProcess.fst"
                             (Prims.of_int (315)) (Prims.of_int (57))
                             (Prims.of_int (315)) (Prims.of_int (74)))))
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range "Prims.fst"
                             (Prims.of_int (611)) (Prims.of_int (19))
                             (Prims.of_int (611)) (Prims.of_int (31)))))
                    (Obj.magic uu___3)
                    (fun uu___4 ->
                       FStar_Tactics_Effect.lift_div_tac
                         (fun uu___5 ->
                            Prims.strcat
                              "[> split_conjunctions_under_match: " uu___4)) in
                FStar_Tactics_Effect.tac_bind
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range
                           "FStar.InteractiveHelpers.PostProcess.fst"
                           (Prims.of_int (315)) (Prims.of_int (16))
                           (Prims.of_int (315)) (Prims.of_int (75)))))
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range
                           "FStar.InteractiveHelpers.PostProcess.fst"
                           (Prims.of_int (315)) (Prims.of_int (2))
                           (Prims.of_int (315)) (Prims.of_int (75)))))
                  (Obj.magic uu___2)
                  (fun uu___3 ->
                     (fun uu___3 ->
                        Obj.magic
                          (FStar_InteractiveHelpers_Base.print_dbg dbg uu___3))
                       uu___3) in
              Obj.magic
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range
                            "FStar.InteractiveHelpers.PostProcess.fst"
                            (Prims.of_int (315)) (Prims.of_int (2))
                            (Prims.of_int (315)) (Prims.of_int (75)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range
                            "FStar.InteractiveHelpers.PostProcess.fst"
                            (Prims.of_int (316)) (Prims.of_int (2))
                            (Prims.of_int (322)) (Prims.of_int (7)))))
                   (Obj.magic uu___1)
                   (fun uu___2 ->
                      (fun uu___2 ->
                         let uu___3 = FStarC_Tactics_V1_Builtins.inspect t1 in
                         Obj.magic
                           (FStar_Tactics_Effect.tac_bind
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "FStar.InteractiveHelpers.PostProcess.fst"
                                       (Prims.of_int (316))
                                       (Prims.of_int (8))
                                       (Prims.of_int (316))
                                       (Prims.of_int (18)))))
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "FStar.InteractiveHelpers.PostProcess.fst"
                                       (Prims.of_int (316))
                                       (Prims.of_int (2))
                                       (Prims.of_int (322))
                                       (Prims.of_int (7)))))
                              (Obj.magic uu___3)
                              (fun uu___4 ->
                                 (fun uu___4 ->
                                    match uu___4 with
                                    | FStarC_Reflection_V1_Data.Tv_Match
                                        (scrut, ret_opt, (pat, br)::[]) ->
                                        Obj.magic
                                          (Obj.repr
                                             (let uu___5 =
                                                split_conjunctions br in
                                              FStar_Tactics_Effect.tac_bind
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "FStar.InteractiveHelpers.PostProcess.fst"
                                                         (Prims.of_int (318))
                                                         (Prims.of_int (13))
                                                         (Prims.of_int (318))
                                                         (Prims.of_int (34)))))
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "FStar.InteractiveHelpers.PostProcess.fst"
                                                         (Prims.of_int (319))
                                                         (Prims.of_int (4))
                                                         (Prims.of_int (319))
                                                         (Prims.of_int (62)))))
                                                (Obj.magic uu___5)
                                                (fun uu___6 ->
                                                   (fun tl ->
                                                      Obj.magic
                                                        (FStar_Tactics_Util.map
                                                           (fun x ->
                                                              FStarC_Tactics_V1_Builtins.pack
                                                                (FStarC_Reflection_V1_Data.Tv_Match
                                                                   (scrut,
                                                                    ret_opt,
                                                                    [
                                                                    (pat, x)])))
                                                           tl)) uu___6)))
                                    | uu___5 ->
                                        Obj.magic
                                          (Obj.repr
                                             (FStar_Tactics_Effect.lift_div_tac
                                                (fun uu___6 -> [t])))) uu___4)))
                        uu___2))) uu___1)
let (split_assert_conjs :
  Prims.bool ->
    FStarC_Reflection_Types.term exploration_result ->
      (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun dbg ->
    fun res ->
      let uu___ =
        Obj.magic (FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> res.ge)) in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range
                 "FStar.InteractiveHelpers.PostProcess.fst"
                 (Prims.of_int (326)) (Prims.of_int (12))
                 (Prims.of_int (326)) (Prims.of_int (18)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range
                 "FStar.InteractiveHelpers.PostProcess.fst"
                 (Prims.of_int (326)) (Prims.of_int (21))
                 (Prims.of_int (341)) (Prims.of_int (30)))))
        (Obj.magic uu___)
        (fun uu___1 ->
           (fun ge0 ->
              let uu___1 =
                FStarC_Tactics_V1_Builtins.norm_term_env
                  ge0.FStar_InteractiveHelpers_Base.env
                  FStar_InteractiveHelpers_Propositions.simpl_norm_steps
                  res.res in
              Obj.magic
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range
                            "FStar.InteractiveHelpers.PostProcess.fst"
                            (Prims.of_int (328)) (Prims.of_int (10))
                            (Prims.of_int (328)) (Prims.of_int (56)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range
                            "FStar.InteractiveHelpers.PostProcess.fst"
                            (Prims.of_int (328)) (Prims.of_int (59))
                            (Prims.of_int (341)) (Prims.of_int (30)))))
                   (Obj.magic uu___1)
                   (fun uu___2 ->
                      (fun t ->
                         let uu___2 = split_conjunctions t in
                         Obj.magic
                           (FStar_Tactics_Effect.tac_bind
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "FStar.InteractiveHelpers.PostProcess.fst"
                                       (Prims.of_int (330))
                                       (Prims.of_int (14))
                                       (Prims.of_int (330))
                                       (Prims.of_int (34)))))
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "FStar.InteractiveHelpers.PostProcess.fst"
                                       (Prims.of_int (330))
                                       (Prims.of_int (37))
                                       (Prims.of_int (341))
                                       (Prims.of_int (30)))))
                              (Obj.magic uu___2)
                              (fun uu___3 ->
                                 (fun conjs ->
                                    let uu___3 =
                                      if
                                        (FStar_List_Tot_Base.length conjs) =
                                          Prims.int_one
                                      then
                                        Obj.magic
                                          (Obj.repr
                                             (split_conjunctions_under_match
                                                dbg t))
                                      else
                                        Obj.magic
                                          (Obj.repr
                                             (FStar_Tactics_Effect.lift_div_tac
                                                (fun uu___5 -> conjs))) in
                                    Obj.magic
                                      (FStar_Tactics_Effect.tac_bind
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "FStar.InteractiveHelpers.PostProcess.fst"
                                                  (Prims.of_int (336))
                                                  (Prims.of_int (4))
                                                  (Prims.of_int (337))
                                                  (Prims.of_int (14)))))
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "FStar.InteractiveHelpers.PostProcess.fst"
                                                  (Prims.of_int (338))
                                                  (Prims.of_int (4))
                                                  (Prims.of_int (341))
                                                  (Prims.of_int (30)))))
                                         (Obj.magic uu___3)
                                         (fun uu___4 ->
                                            (fun conjs1 ->
                                               let uu___4 =
                                                 Obj.magic
                                                   (FStar_Tactics_Effect.lift_div_tac
                                                      (fun uu___5 ->
                                                         FStar_InteractiveHelpers_Propositions.mk_assertions
                                                           conjs1 [])) in
                                               Obj.magic
                                                 (FStar_Tactics_Effect.tac_bind
                                                    (FStar_Sealed.seal
                                                       (Obj.magic
                                                          (FStar_Range.mk_range
                                                             "FStar.InteractiveHelpers.PostProcess.fst"
                                                             (Prims.of_int (339))
                                                             (Prims.of_int (16))
                                                             (Prims.of_int (339))
                                                             (Prims.of_int (38)))))
                                                    (FStar_Sealed.seal
                                                       (Obj.magic
                                                          (FStar_Range.mk_range
                                                             "FStar.InteractiveHelpers.PostProcess.fst"
                                                             (Prims.of_int (341))
                                                             (Prims.of_int (2))
                                                             (Prims.of_int (341))
                                                             (Prims.of_int (30)))))
                                                    (Obj.magic uu___4)
                                                    (fun uu___5 ->
                                                       (fun asserts ->
                                                          Obj.magic
                                                            (FStar_InteractiveHelpers_Output.printout_success
                                                               ge0 asserts))
                                                         uu___5))) uu___4)))
                                   uu___3))) uu___2))) uu___1)
let (pp_split_assert_conjs :
  Prims.bool -> unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun dbg ->
    fun uu___ ->
      FStar_Tactics_V1_Derived.try_with
        (fun uu___1 ->
           match () with
           | () ->
               let uu___2 = find_focused_assert_in_current_goal dbg in
               FStar_Tactics_Effect.tac_bind
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range
                          "FStar.InteractiveHelpers.PostProcess.fst"
                          (Prims.of_int (347)) (Prims.of_int (14))
                          (Prims.of_int (347)) (Prims.of_int (53)))))
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range
                          "FStar.InteractiveHelpers.PostProcess.fst"
                          (Prims.of_int (348)) (Prims.of_int (4))
                          (Prims.of_int (349)) (Prims.of_int (16)))))
                 (Obj.magic uu___2)
                 (fun uu___3 ->
                    (fun res ->
                       let uu___3 = split_assert_conjs dbg res in
                       Obj.magic
                         (FStar_Tactics_Effect.tac_bind
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.InteractiveHelpers.PostProcess.fst"
                                     (Prims.of_int (348)) (Prims.of_int (4))
                                     (Prims.of_int (348)) (Prims.of_int (30)))))
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.InteractiveHelpers.PostProcess.fst"
                                     (Prims.of_int (349)) (Prims.of_int (4))
                                     (Prims.of_int (349)) (Prims.of_int (16)))))
                            (Obj.magic uu___3)
                            (fun uu___4 ->
                               (fun uu___4 -> Obj.magic (end_proof ()))
                                 uu___4))) uu___3))
        (fun uu___1 ->
           (fun uu___1 ->
              match uu___1 with
              | FStar_InteractiveHelpers_Base.MetaAnalysis msg ->
                  Obj.magic
                    (Obj.repr
                       (let uu___2 =
                          FStar_InteractiveHelpers_Output.printout_failure
                            msg in
                        FStar_Tactics_Effect.tac_bind
                          (FStar_Sealed.seal
                             (Obj.magic
                                (FStar_Range.mk_range
                                   "FStar.InteractiveHelpers.PostProcess.fst"
                                   (Prims.of_int (350)) (Prims.of_int (29))
                                   (Prims.of_int (350)) (Prims.of_int (49)))))
                          (FStar_Sealed.seal
                             (Obj.magic
                                (FStar_Range.mk_range
                                   "FStar.InteractiveHelpers.PostProcess.fst"
                                   (Prims.of_int (350)) (Prims.of_int (51))
                                   (Prims.of_int (350)) (Prims.of_int (63)))))
                          (Obj.magic uu___2)
                          (fun uu___3 ->
                             (fun uu___3 -> Obj.magic (end_proof ())) uu___3)))
              | err -> Obj.magic (Obj.repr (FStar_Tactics_Effect.raise err)))
             uu___1)
let _ =
  FStarC_Tactics_Native.register_tactic
    "FStar.InteractiveHelpers.PostProcess.pp_split_assert_conjs"
    (Prims.of_int (3))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             FStarC_Tactics_InterpFuns.mk_tactic_interpretation_2
               "FStar.InteractiveHelpers.PostProcess.pp_split_assert_conjs (plugin)"
               (FStarC_Tactics_Native.from_tactic_2 pp_split_assert_conjs)
               FStarC_Syntax_Embeddings.e_bool
               FStarC_Syntax_Embeddings.e_unit
               FStarC_Syntax_Embeddings.e_unit psc ncb us args)
type eq_kind =
  | Eq_Dec of FStarC_Reflection_Types.typ 
  | Eq_Undec of FStarC_Reflection_Types.typ 
  | Eq_Hetero of FStarC_Reflection_Types.typ * FStarC_Reflection_Types.typ 
let (uu___is_Eq_Dec : eq_kind -> Prims.bool) =
  fun projectee -> match projectee with | Eq_Dec _0 -> true | uu___ -> false
let (__proj__Eq_Dec__item___0 : eq_kind -> FStarC_Reflection_Types.typ) =
  fun projectee -> match projectee with | Eq_Dec _0 -> _0
let (uu___is_Eq_Undec : eq_kind -> Prims.bool) =
  fun projectee ->
    match projectee with | Eq_Undec _0 -> true | uu___ -> false
let (__proj__Eq_Undec__item___0 : eq_kind -> FStarC_Reflection_Types.typ) =
  fun projectee -> match projectee with | Eq_Undec _0 -> _0
let (uu___is_Eq_Hetero : eq_kind -> Prims.bool) =
  fun projectee ->
    match projectee with | Eq_Hetero (_0, _1) -> true | uu___ -> false
let (__proj__Eq_Hetero__item___0 : eq_kind -> FStarC_Reflection_Types.typ) =
  fun projectee -> match projectee with | Eq_Hetero (_0, _1) -> _0
let (__proj__Eq_Hetero__item___1 : eq_kind -> FStarC_Reflection_Types.typ) =
  fun projectee -> match projectee with | Eq_Hetero (_0, _1) -> _1
let (is_eq :
  Prims.bool ->
    FStarC_Reflection_Types.term ->
      ((eq_kind * FStarC_Reflection_Types.term *
         FStarC_Reflection_Types.term) FStar_Pervasives_Native.option,
        unit) FStar_Tactics_Effect.tac_repr)
  =
  fun dbg ->
    fun t ->
      let uu___ = remove_b2t t in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range
                 "FStar.InteractiveHelpers.PostProcess.fst"
                 (Prims.of_int (371)) (Prims.of_int (10))
                 (Prims.of_int (371)) (Prims.of_int (22)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range
                 "FStar.InteractiveHelpers.PostProcess.fst"
                 (Prims.of_int (372)) (Prims.of_int (2)) (Prims.of_int (391))
                 (Prims.of_int (13))))) (Obj.magic uu___)
        (fun uu___1 ->
           (fun t1 ->
              let uu___1 =
                let uu___2 =
                  let uu___3 = FStarC_Tactics_V1_Builtins.term_to_string t1 in
                  FStar_Tactics_Effect.tac_bind
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range
                             "FStar.InteractiveHelpers.PostProcess.fst"
                             (Prims.of_int (372)) (Prims.of_int (32))
                             (Prims.of_int (372)) (Prims.of_int (48)))))
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range "Prims.fst"
                             (Prims.of_int (611)) (Prims.of_int (19))
                             (Prims.of_int (611)) (Prims.of_int (31)))))
                    (Obj.magic uu___3)
                    (fun uu___4 ->
                       FStar_Tactics_Effect.lift_div_tac
                         (fun uu___5 -> Prims.strcat "[> is_eq: " uu___4)) in
                FStar_Tactics_Effect.tac_bind
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range
                           "FStar.InteractiveHelpers.PostProcess.fst"
                           (Prims.of_int (372)) (Prims.of_int (16))
                           (Prims.of_int (372)) (Prims.of_int (49)))))
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range
                           "FStar.InteractiveHelpers.PostProcess.fst"
                           (Prims.of_int (372)) (Prims.of_int (2))
                           (Prims.of_int (372)) (Prims.of_int (49)))))
                  (Obj.magic uu___2)
                  (fun uu___3 ->
                     (fun uu___3 ->
                        Obj.magic
                          (FStar_InteractiveHelpers_Base.print_dbg dbg uu___3))
                       uu___3) in
              Obj.magic
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range
                            "FStar.InteractiveHelpers.PostProcess.fst"
                            (Prims.of_int (372)) (Prims.of_int (2))
                            (Prims.of_int (372)) (Prims.of_int (49)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range
                            "FStar.InteractiveHelpers.PostProcess.fst"
                            (Prims.of_int (372)) (Prims.of_int (50))
                            (Prims.of_int (391)) (Prims.of_int (13)))))
                   (Obj.magic uu___1)
                   (fun uu___2 ->
                      (fun uu___2 ->
                         let uu___3 =
                           FStar_Tactics_V1_SyntaxHelpers.collect_app t1 in
                         Obj.magic
                           (FStar_Tactics_Effect.tac_bind
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "FStar.InteractiveHelpers.PostProcess.fst"
                                       (Prims.of_int (373))
                                       (Prims.of_int (19))
                                       (Prims.of_int (373))
                                       (Prims.of_int (32)))))
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "FStar.InteractiveHelpers.PostProcess.fst"
                                       (Prims.of_int (372))
                                       (Prims.of_int (50))
                                       (Prims.of_int (391))
                                       (Prims.of_int (13)))))
                              (Obj.magic uu___3)
                              (fun uu___4 ->
                                 (fun uu___4 ->
                                    match uu___4 with
                                    | (hd, params) ->
                                        let uu___5 =
                                          let uu___6 =
                                            let uu___7 =
                                              FStarC_Tactics_V1_Builtins.term_to_string
                                                hd in
                                            FStar_Tactics_Effect.tac_bind
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "FStar.InteractiveHelpers.PostProcess.fst"
                                                       (Prims.of_int (374))
                                                       (Prims.of_int (29))
                                                       (Prims.of_int (374))
                                                       (Prims.of_int (46)))))
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
                                                      Prims.strcat "- hd:\n"
                                                        uu___8)) in
                                          FStar_Tactics_Effect.tac_bind
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "FStar.InteractiveHelpers.PostProcess.fst"
                                                     (Prims.of_int (374))
                                                     (Prims.of_int (16))
                                                     (Prims.of_int (374))
                                                     (Prims.of_int (47)))))
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "FStar.InteractiveHelpers.PostProcess.fst"
                                                     (Prims.of_int (374))
                                                     (Prims.of_int (2))
                                                     (Prims.of_int (374))
                                                     (Prims.of_int (47)))))
                                            (Obj.magic uu___6)
                                            (fun uu___7 ->
                                               (fun uu___7 ->
                                                  Obj.magic
                                                    (FStar_InteractiveHelpers_Base.print_dbg
                                                       dbg uu___7)) uu___7) in
                                        Obj.magic
                                          (FStar_Tactics_Effect.tac_bind
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "FStar.InteractiveHelpers.PostProcess.fst"
                                                      (Prims.of_int (374))
                                                      (Prims.of_int (2))
                                                      (Prims.of_int (374))
                                                      (Prims.of_int (47)))))
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "FStar.InteractiveHelpers.PostProcess.fst"
                                                      (Prims.of_int (375))
                                                      (Prims.of_int (2))
                                                      (Prims.of_int (391))
                                                      (Prims.of_int (13)))))
                                             (Obj.magic uu___5)
                                             (fun uu___6 ->
                                                (fun uu___6 ->
                                                   let uu___7 =
                                                     let uu___8 =
                                                       let uu___9 =
                                                         FStar_InteractiveHelpers_Base.list_to_string
                                                           (fun uu___10 ->
                                                              match uu___10
                                                              with
                                                              | (x, y) ->
                                                                  FStarC_Tactics_V1_Builtins.term_to_string
                                                                    x) params in
                                                       FStar_Tactics_Effect.tac_bind
                                                         (FStar_Sealed.seal
                                                            (Obj.magic
                                                               (FStar_Range.mk_range
                                                                  "FStar.InteractiveHelpers.PostProcess.fst"
                                                                  (Prims.of_int (375))
                                                                  (Prims.of_int (37))
                                                                  (Prims.of_int (375))
                                                                  (Prims.of_int (91)))))
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
                                                                   "- parameters:\n"
                                                                   uu___10)) in
                                                     FStar_Tactics_Effect.tac_bind
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "FStar.InteractiveHelpers.PostProcess.fst"
                                                                (Prims.of_int (375))
                                                                (Prims.of_int (16))
                                                                (Prims.of_int (375))
                                                                (Prims.of_int (92)))))
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "FStar.InteractiveHelpers.PostProcess.fst"
                                                                (Prims.of_int (375))
                                                                (Prims.of_int (2))
                                                                (Prims.of_int (375))
                                                                (Prims.of_int (92)))))
                                                       (Obj.magic uu___8)
                                                       (fun uu___9 ->
                                                          (fun uu___9 ->
                                                             Obj.magic
                                                               (FStar_InteractiveHelpers_Base.print_dbg
                                                                  dbg uu___9))
                                                            uu___9) in
                                                   Obj.magic
                                                     (FStar_Tactics_Effect.tac_bind
                                                        (FStar_Sealed.seal
                                                           (Obj.magic
                                                              (FStar_Range.mk_range
                                                                 "FStar.InteractiveHelpers.PostProcess.fst"
                                                                 (Prims.of_int (375))
                                                                 (Prims.of_int (2))
                                                                 (Prims.of_int (375))
                                                                 (Prims.of_int (92)))))
                                                        (FStar_Sealed.seal
                                                           (Obj.magic
                                                              (FStar_Range.mk_range
                                                                 "FStar.InteractiveHelpers.PostProcess.fst"
                                                                 (Prims.of_int (376))
                                                                 (Prims.of_int (2))
                                                                 (Prims.of_int (391))
                                                                 (Prims.of_int (13)))))
                                                        (Obj.magic uu___7)
                                                        (fun uu___8 ->
                                                           (fun uu___8 ->
                                                              let uu___9 =
                                                                FStarC_Tactics_V1_Builtins.inspect
                                                                  hd in
                                                              Obj.magic
                                                                (FStar_Tactics_Effect.tac_bind
                                                                   (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (376))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (376))
                                                                    (Prims.of_int (18)))))
                                                                   (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (376))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (391))
                                                                    (Prims.of_int (13)))))
                                                                   (Obj.magic
                                                                    uu___9)
                                                                   (fun
                                                                    uu___10
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    match uu___10
                                                                    with
                                                                    | 
                                                                    FStarC_Reflection_V1_Data.Tv_FVar
                                                                    fv ->
                                                                    (match params
                                                                    with
                                                                    | 
                                                                    (a,
                                                                    FStarC_Reflection_V1_Data.Q_Implicit)::
                                                                    (x,
                                                                    FStarC_Reflection_V1_Data.Q_Explicit)::
                                                                    (y,
                                                                    FStarC_Reflection_V1_Data.Q_Explicit)::[]
                                                                    ->
                                                                    if
                                                                    FStar_Reflection_V1_Derived.is_any_fvar
                                                                    a
                                                                    ["Prims.op_Equality";
                                                                    "Prims.equals";
                                                                    "Prims.op_Equals"]
                                                                    then
                                                                    FStar_Pervasives_Native.Some
                                                                    ((Eq_Dec
                                                                    a), x, y)
                                                                    else
                                                                    if
                                                                    FStar_Reflection_V1_Derived.is_any_fvar
                                                                    a
                                                                    ["Prims.eq2";
                                                                    "Prims.op_Equals_Equals"]
                                                                    then
                                                                    FStar_Pervasives_Native.Some
                                                                    ((Eq_Undec
                                                                    a), x, y)
                                                                    else
                                                                    FStar_Pervasives_Native.None
                                                                    | 
                                                                    (a,
                                                                    FStarC_Reflection_V1_Data.Q_Implicit)::
                                                                    (b,
                                                                    FStarC_Reflection_V1_Data.Q_Implicit)::
                                                                    (x,
                                                                    FStarC_Reflection_V1_Data.Q_Explicit)::
                                                                    (y,
                                                                    FStarC_Reflection_V1_Data.Q_Explicit)::[]
                                                                    ->
                                                                    if
                                                                    FStar_Reflection_V1_Derived.is_fvar
                                                                    a
                                                                    "Prims.op_Equals_Equals_Equals"
                                                                    then
                                                                    FStar_Pervasives_Native.Some
                                                                    ((Eq_Hetero
                                                                    (a, b)),
                                                                    x, y)
                                                                    else
                                                                    FStar_Pervasives_Native.None
                                                                    | 
                                                                    uu___12
                                                                    ->
                                                                    FStar_Pervasives_Native.None)
                                                                    | 
                                                                    uu___12
                                                                    ->
                                                                    FStar_Pervasives_Native.None))))
                                                             uu___8))) uu___6)))
                                   uu___4))) uu___2))) uu___1)
let (mk_eq :
  eq_kind ->
    FStarC_Reflection_Types.term ->
      FStarC_Reflection_Types.term -> FStarC_Reflection_Types.term)
  =
  fun k ->
    fun t1 ->
      fun t2 ->
        match k with
        | Eq_Dec ty ->
            FStar_Reflection_V1_Derived.mk_app
              (FStarC_Reflection_V2_Builtins.pack_ln
                 (FStarC_Reflection_V2_Data.Tv_FVar
                    (FStarC_Reflection_V2_Builtins.pack_fv
                       ["Prims"; "op_Equality"])))
              [(ty, FStarC_Reflection_V1_Data.Q_Implicit);
              (t1, FStarC_Reflection_V1_Data.Q_Explicit);
              (t2, FStarC_Reflection_V1_Data.Q_Explicit)]
        | Eq_Undec ty ->
            FStar_Reflection_V1_Derived.mk_app
              (FStarC_Reflection_V2_Builtins.pack_ln
                 (FStarC_Reflection_V2_Data.Tv_FVar
                    (FStarC_Reflection_V2_Builtins.pack_fv ["Prims"; "eq2"])))
              [(ty, FStarC_Reflection_V1_Data.Q_Implicit);
              (t1, FStarC_Reflection_V1_Data.Q_Explicit);
              (t2, FStarC_Reflection_V1_Data.Q_Explicit)]
        | Eq_Hetero (ty1, ty2) ->
            FStar_Reflection_V1_Derived.mk_app
              (FStarC_Reflection_V2_Builtins.pack_ln
                 (FStarC_Reflection_V2_Data.Tv_FVar
                    (FStarC_Reflection_V2_Builtins.pack_fv
                       ["Prims"; "op_Equals_Equals_Equals"])))
              [(ty1, FStarC_Reflection_V1_Data.Q_Implicit);
              (ty2, FStarC_Reflection_V1_Data.Q_Implicit);
              (t1, FStarC_Reflection_V1_Data.Q_Explicit);
              (t2, FStarC_Reflection_V1_Data.Q_Explicit)]
let (formula_construct :
  FStar_Reflection_V1_Formula.formula ->
    (Prims.string, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___ ->
    (fun f ->
       Obj.magic
         (FStar_Tactics_Effect.lift_div_tac
            (fun uu___ ->
               match f with
               | FStar_Reflection_V1_Formula.True_ -> "True_"
               | FStar_Reflection_V1_Formula.False_ -> "False_"
               | FStar_Reflection_V1_Formula.Comp (uu___1, uu___2, uu___3) ->
                   "Comp"
               | FStar_Reflection_V1_Formula.And (uu___1, uu___2) -> "And"
               | FStar_Reflection_V1_Formula.Or (uu___1, uu___2) -> "Or"
               | FStar_Reflection_V1_Formula.Not uu___1 -> "Not"
               | FStar_Reflection_V1_Formula.Implies (uu___1, uu___2) ->
                   "Implies"
               | FStar_Reflection_V1_Formula.Iff (uu___1, uu___2) -> "Iff"
               | FStar_Reflection_V1_Formula.Forall (uu___1, uu___2, uu___3)
                   -> "Forall"
               | FStar_Reflection_V1_Formula.Exists (uu___1, uu___2, uu___3)
                   -> "Exists"
               | FStar_Reflection_V1_Formula.App (uu___1, uu___2) -> "Apply"
               | FStar_Reflection_V1_Formula.Name uu___1 -> "Name"
               | FStar_Reflection_V1_Formula.FV uu___1 -> "FV"
               | FStar_Reflection_V1_Formula.IntLit uu___1 -> "IntLit"
               | FStar_Reflection_V1_Formula.F_Unknown -> "F_Unknown")))
      uu___
let (is_equality_for_term :
  Prims.bool ->
    FStarC_Reflection_Types.term ->
      FStarC_Reflection_Types.term ->
        (FStarC_Reflection_Types.term FStar_Pervasives_Native.option, 
          unit) FStar_Tactics_Effect.tac_repr)
  =
  fun dbg ->
    fun tm ->
      fun p ->
        let uu___ =
          let uu___1 =
            let uu___2 =
              let uu___3 =
                let uu___4 = FStarC_Tactics_V1_Builtins.term_to_string tm in
                FStar_Tactics_Effect.tac_bind
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range
                           "FStar.InteractiveHelpers.PostProcess.fst"
                           (Prims.of_int (428)) (Prims.of_int (32))
                           (Prims.of_int (428)) (Prims.of_int (49)))))
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range
                           "FStar.InteractiveHelpers.PostProcess.fst"
                           (Prims.of_int (428)) (Prims.of_int (32))
                           (Prims.of_int (429)) (Prims.of_int (48)))))
                  (Obj.magic uu___4)
                  (fun uu___5 ->
                     (fun uu___5 ->
                        let uu___6 =
                          let uu___7 =
                            FStarC_Tactics_V1_Builtins.term_to_string p in
                          FStar_Tactics_Effect.tac_bind
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.InteractiveHelpers.PostProcess.fst"
                                     (Prims.of_int (429)) (Prims.of_int (32))
                                     (Prims.of_int (429)) (Prims.of_int (48)))))
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range "Prims.fst"
                                     (Prims.of_int (611)) (Prims.of_int (19))
                                     (Prims.of_int (611)) (Prims.of_int (31)))))
                            (Obj.magic uu___7)
                            (fun uu___8 ->
                               FStar_Tactics_Effect.lift_div_tac
                                 (fun uu___9 ->
                                    Prims.strcat "\n- prop: " uu___8)) in
                        Obj.magic
                          (FStar_Tactics_Effect.tac_bind
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "FStar.InteractiveHelpers.PostProcess.fst"
                                      (Prims.of_int (429))
                                      (Prims.of_int (17))
                                      (Prims.of_int (429))
                                      (Prims.of_int (48)))))
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
                                  (fun uu___8 -> Prims.strcat uu___5 uu___7))))
                       uu___5) in
              FStar_Tactics_Effect.tac_bind
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range
                         "FStar.InteractiveHelpers.PostProcess.fst"
                         (Prims.of_int (428)) (Prims.of_int (32))
                         (Prims.of_int (429)) (Prims.of_int (48)))))
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Prims.fst" (Prims.of_int (611))
                         (Prims.of_int (19)) (Prims.of_int (611))
                         (Prims.of_int (31))))) (Obj.magic uu___3)
                (fun uu___4 ->
                   FStar_Tactics_Effect.lift_div_tac
                     (fun uu___5 -> Prims.strcat "\n- term: " uu___4)) in
            FStar_Tactics_Effect.tac_bind
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range
                       "FStar.InteractiveHelpers.PostProcess.fst"
                       (Prims.of_int (428)) (Prims.of_int (17))
                       (Prims.of_int (429)) (Prims.of_int (48)))))
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "Prims.fst" (Prims.of_int (611))
                       (Prims.of_int (19)) (Prims.of_int (611))
                       (Prims.of_int (31))))) (Obj.magic uu___2)
              (fun uu___3 ->
                 FStar_Tactics_Effect.lift_div_tac
                   (fun uu___4 ->
                      Prims.strcat "[> is_equality_for_term:" uu___3)) in
          FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range
                     "FStar.InteractiveHelpers.PostProcess.fst"
                     (Prims.of_int (427)) (Prims.of_int (16))
                     (Prims.of_int (429)) (Prims.of_int (49)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range
                     "FStar.InteractiveHelpers.PostProcess.fst"
                     (Prims.of_int (427)) (Prims.of_int (2))
                     (Prims.of_int (429)) (Prims.of_int (49)))))
            (Obj.magic uu___1)
            (fun uu___2 ->
               (fun uu___2 ->
                  Obj.magic
                    (FStar_InteractiveHelpers_Base.print_dbg dbg uu___2))
                 uu___2) in
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range
                   "FStar.InteractiveHelpers.PostProcess.fst"
                   (Prims.of_int (427)) (Prims.of_int (2))
                   (Prims.of_int (429)) (Prims.of_int (49)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range
                   "FStar.InteractiveHelpers.PostProcess.fst"
                   (Prims.of_int (429)) (Prims.of_int (50))
                   (Prims.of_int (453)) (Prims.of_int (8)))))
          (Obj.magic uu___)
          (fun uu___1 ->
             (fun uu___1 ->
                let uu___2 =
                  let uu___3 = FStarC_Tactics_V1_Builtins.inspect tm in
                  FStar_Tactics_Effect.tac_bind
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range
                             "FStar.InteractiveHelpers.PostProcess.fst"
                             (Prims.of_int (433)) (Prims.of_int (10))
                             (Prims.of_int (433)) (Prims.of_int (20)))))
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range
                             "FStar.InteractiveHelpers.PostProcess.fst"
                             (Prims.of_int (433)) (Prims.of_int (4))
                             (Prims.of_int (436)) (Prims.of_int (38)))))
                    (Obj.magic uu___3)
                    (fun uu___4 ->
                       FStar_Tactics_Effect.lift_div_tac
                         (fun uu___6 ->
                            fun uu___5 ->
                              (fun uu___5 ->
                                 match uu___4 with
                                 | FStarC_Reflection_V1_Data.Tv_Var bv ->
                                     Obj.magic
                                       (Obj.repr
                                          (fun tm' ->
                                             let uu___6 =
                                               FStarC_Tactics_V1_Builtins.inspect
                                                 tm' in
                                             FStar_Tactics_Effect.tac_bind
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "FStar.InteractiveHelpers.PostProcess.fst"
                                                        (Prims.of_int (435))
                                                        (Prims.of_int (24))
                                                        (Prims.of_int (435))
                                                        (Prims.of_int (35)))))
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "FStar.InteractiveHelpers.PostProcess.fst"
                                                        (Prims.of_int (435))
                                                        (Prims.of_int (18))
                                                        (Prims.of_int (435))
                                                        (Prims.of_int (82)))))
                                               (Obj.magic uu___6)
                                               (fun uu___7 ->
                                                  FStar_Tactics_Effect.lift_div_tac
                                                    (fun uu___8 ->
                                                       match uu___7 with
                                                       | FStarC_Reflection_V1_Data.Tv_Var
                                                           bv' ->
                                                           FStar_InteractiveHelpers_Base.bv_eq
                                                             bv bv'
                                                       | uu___9 -> false))))
                                 | uu___6 ->
                                     Obj.magic
                                       (Obj.repr
                                          (fun tm' ->
                                             FStar_Tactics_Effect.lift_div_tac
                                               (fun uu___7 ->
                                                  FStar_InteractiveHelpers_Effectful.term_eq
                                                    tm tm')))) uu___6 uu___5)) in
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "FStar.InteractiveHelpers.PostProcess.fst"
                              (Prims.of_int (433)) (Prims.of_int (4))
                              (Prims.of_int (436)) (Prims.of_int (38)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "FStar.InteractiveHelpers.PostProcess.fst"
                              (Prims.of_int (438)) (Prims.of_int (2))
                              (Prims.of_int (453)) (Prims.of_int (8)))))
                     (Obj.magic uu___2)
                     (fun uu___3 ->
                        (fun check_eq ->
                           let uu___3 = is_eq dbg p in
                           Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "FStar.InteractiveHelpers.PostProcess.fst"
                                         (Prims.of_int (438))
                                         (Prims.of_int (8))
                                         (Prims.of_int (438))
                                         (Prims.of_int (19)))))
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "FStar.InteractiveHelpers.PostProcess.fst"
                                         (Prims.of_int (438))
                                         (Prims.of_int (2))
                                         (Prims.of_int (453))
                                         (Prims.of_int (8)))))
                                (Obj.magic uu___3)
                                (fun uu___4 ->
                                   (fun uu___4 ->
                                      match uu___4 with
                                      | FStar_Pervasives_Native.Some
                                          (ekind, l, r) ->
                                          let uu___5 =
                                            let uu___6 =
                                              let uu___7 =
                                                let uu___8 =
                                                  FStarC_Tactics_V1_Builtins.term_to_string
                                                    l in
                                                FStar_Tactics_Effect.tac_bind
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "FStar.InteractiveHelpers.PostProcess.fst"
                                                           (Prims.of_int (442))
                                                           (Prims.of_int (36))
                                                           (Prims.of_int (442))
                                                           (Prims.of_int (52)))))
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "FStar.InteractiveHelpers.PostProcess.fst"
                                                           (Prims.of_int (442))
                                                           (Prims.of_int (36))
                                                           (Prims.of_int (442))
                                                           (Prims.of_int (79)))))
                                                  (Obj.magic uu___8)
                                                  (fun uu___9 ->
                                                     (fun uu___9 ->
                                                        let uu___10 =
                                                          let uu___11 =
                                                            FStarC_Tactics_V1_Builtins.term_to_string
                                                              r in
                                                          FStar_Tactics_Effect.tac_bind
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (442))
                                                                    (Prims.of_int (63))
                                                                    (Prims.of_int (442))
                                                                    (Prims.of_int (79)))))
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
                                                            (fun uu___12 ->
                                                               FStar_Tactics_Effect.lift_div_tac
                                                                 (fun uu___13
                                                                    ->
                                                                    Prims.strcat
                                                                    " = "
                                                                    uu___12)) in
                                                        Obj.magic
                                                          (FStar_Tactics_Effect.tac_bind
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (442))
                                                                    (Prims.of_int (55))
                                                                    (Prims.of_int (442))
                                                                    (Prims.of_int (79)))))
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
                                                             (fun uu___11 ->
                                                                FStar_Tactics_Effect.lift_div_tac
                                                                  (fun
                                                                    uu___12
                                                                    ->
                                                                    Prims.strcat
                                                                    uu___9
                                                                    uu___11))))
                                                       uu___9) in
                                              FStar_Tactics_Effect.tac_bind
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "FStar.InteractiveHelpers.PostProcess.fst"
                                                         (Prims.of_int (442))
                                                         (Prims.of_int (36))
                                                         (Prims.of_int (442))
                                                         (Prims.of_int (79)))))
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
                                                          "Term is eq: "
                                                          uu___8)) in
                                            FStar_Tactics_Effect.tac_bind
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "FStar.InteractiveHelpers.PostProcess.fst"
                                                       (Prims.of_int (442))
                                                       (Prims.of_int (18))
                                                       (Prims.of_int (442))
                                                       (Prims.of_int (80)))))
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "FStar.InteractiveHelpers.PostProcess.fst"
                                                       (Prims.of_int (442))
                                                       (Prims.of_int (4))
                                                       (Prims.of_int (442))
                                                       (Prims.of_int (80)))))
                                              (Obj.magic uu___6)
                                              (fun uu___7 ->
                                                 (fun uu___7 ->
                                                    Obj.magic
                                                      (FStar_InteractiveHelpers_Base.print_dbg
                                                         dbg uu___7)) uu___7) in
                                          Obj.magic
                                            (FStar_Tactics_Effect.tac_bind
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "FStar.InteractiveHelpers.PostProcess.fst"
                                                        (Prims.of_int (442))
                                                        (Prims.of_int (4))
                                                        (Prims.of_int (442))
                                                        (Prims.of_int (80)))))
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "FStar.InteractiveHelpers.PostProcess.fst"
                                                        (Prims.of_int (443))
                                                        (Prims.of_int (4))
                                                        (Prims.of_int (450))
                                                        (Prims.of_int (13)))))
                                               (Obj.magic uu___5)
                                               (fun uu___6 ->
                                                  (fun uu___6 ->
                                                     if
                                                       uu___is_Eq_Hetero
                                                         ekind
                                                     then
                                                       let uu___7 =
                                                         FStar_InteractiveHelpers_Base.print_dbg
                                                           dbg
                                                           "Ignoring heterogeneous equality" in
                                                       Obj.magic
                                                         (FStar_Tactics_Effect.tac_bind
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (445))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (445))
                                                                    (Prims.of_int (53)))))
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (446))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (446))
                                                                    (Prims.of_int (10)))))
                                                            (Obj.magic uu___7)
                                                            (fun uu___8 ->
                                                               FStar_Tactics_Effect.lift_div_tac
                                                                 (fun uu___9
                                                                    ->
                                                                    FStar_Pervasives_Native.None)))
                                                     else
                                                       (let uu___8 =
                                                          check_eq l in
                                                        Obj.magic
                                                          (FStar_Tactics_Effect.tac_bind
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (448))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (448))
                                                                    (Prims.of_int (22)))))
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (448))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (450))
                                                                    (Prims.of_int (13)))))
                                                             (Obj.magic
                                                                uu___8)
                                                             (fun uu___9 ->
                                                                (fun uu___9
                                                                   ->
                                                                   if uu___9
                                                                   then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    FStar_Pervasives_Native.Some
                                                                    r)))
                                                                   else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (let uu___11
                                                                    =
                                                                    check_eq
                                                                    r in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (449))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (449))
                                                                    (Prims.of_int (22)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (449))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (450))
                                                                    (Prims.of_int (13)))))
                                                                    (Obj.magic
                                                                    uu___11)
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    if
                                                                    uu___12
                                                                    then
                                                                    FStar_Pervasives_Native.Some
                                                                    l
                                                                    else
                                                                    FStar_Pervasives_Native.None)))))
                                                                  uu___9))))
                                                    uu___6))
                                      | uu___5 ->
                                          let uu___6 =
                                            FStar_InteractiveHelpers_Base.print_dbg
                                              dbg "Term is not eq" in
                                          Obj.magic
                                            (FStar_Tactics_Effect.tac_bind
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "FStar.InteractiveHelpers.PostProcess.fst"
                                                        (Prims.of_int (452))
                                                        (Prims.of_int (4))
                                                        (Prims.of_int (452))
                                                        (Prims.of_int (34)))))
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "FStar.InteractiveHelpers.PostProcess.fst"
                                                        (Prims.of_int (453))
                                                        (Prims.of_int (4))
                                                        (Prims.of_int (453))
                                                        (Prims.of_int (8)))))
                                               (Obj.magic uu___6)
                                               (fun uu___7 ->
                                                  FStar_Tactics_Effect.lift_div_tac
                                                    (fun uu___8 ->
                                                       FStar_Pervasives_Native.None))))
                                     uu___4))) uu___3))) uu___1)
let (find_subequality :
  Prims.bool ->
    FStarC_Reflection_Types.term ->
      FStarC_Reflection_Types.term ->
        (FStarC_Reflection_Types.term FStar_Pervasives_Native.option, 
          unit) FStar_Tactics_Effect.tac_repr)
  =
  fun dbg ->
    fun tm ->
      fun p ->
        let uu___ =
          let uu___1 =
            let uu___2 =
              let uu___3 =
                let uu___4 = FStarC_Tactics_V1_Builtins.term_to_string tm in
                FStar_Tactics_Effect.tac_bind
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range
                           "FStar.InteractiveHelpers.PostProcess.fst"
                           (Prims.of_int (458)) (Prims.of_int (33))
                           (Prims.of_int (458)) (Prims.of_int (50)))))
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range
                           "FStar.InteractiveHelpers.PostProcess.fst"
                           (Prims.of_int (458)) (Prims.of_int (33))
                           (Prims.of_int (459)) (Prims.of_int (49)))))
                  (Obj.magic uu___4)
                  (fun uu___5 ->
                     (fun uu___5 ->
                        let uu___6 =
                          let uu___7 =
                            FStarC_Tactics_V1_Builtins.term_to_string p in
                          FStar_Tactics_Effect.tac_bind
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.InteractiveHelpers.PostProcess.fst"
                                     (Prims.of_int (459)) (Prims.of_int (33))
                                     (Prims.of_int (459)) (Prims.of_int (49)))))
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range "Prims.fst"
                                     (Prims.of_int (611)) (Prims.of_int (19))
                                     (Prims.of_int (611)) (Prims.of_int (31)))))
                            (Obj.magic uu___7)
                            (fun uu___8 ->
                               FStar_Tactics_Effect.lift_div_tac
                                 (fun uu___9 ->
                                    Prims.strcat "\n- props: " uu___8)) in
                        Obj.magic
                          (FStar_Tactics_Effect.tac_bind
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "FStar.InteractiveHelpers.PostProcess.fst"
                                      (Prims.of_int (459))
                                      (Prims.of_int (17))
                                      (Prims.of_int (459))
                                      (Prims.of_int (49)))))
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
                                  (fun uu___8 -> Prims.strcat uu___5 uu___7))))
                       uu___5) in
              FStar_Tactics_Effect.tac_bind
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range
                         "FStar.InteractiveHelpers.PostProcess.fst"
                         (Prims.of_int (458)) (Prims.of_int (33))
                         (Prims.of_int (459)) (Prims.of_int (49)))))
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range "Prims.fst" (Prims.of_int (611))
                         (Prims.of_int (19)) (Prims.of_int (611))
                         (Prims.of_int (31))))) (Obj.magic uu___3)
                (fun uu___4 ->
                   FStar_Tactics_Effect.lift_div_tac
                     (fun uu___5 -> Prims.strcat "\n- ter  : " uu___4)) in
            FStar_Tactics_Effect.tac_bind
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range
                       "FStar.InteractiveHelpers.PostProcess.fst"
                       (Prims.of_int (458)) (Prims.of_int (17))
                       (Prims.of_int (459)) (Prims.of_int (49)))))
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range "Prims.fst" (Prims.of_int (611))
                       (Prims.of_int (19)) (Prims.of_int (611))
                       (Prims.of_int (31))))) (Obj.magic uu___2)
              (fun uu___3 ->
                 FStar_Tactics_Effect.lift_div_tac
                   (fun uu___4 -> Prims.strcat "[> find_subequality:" uu___3)) in
          FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range
                     "FStar.InteractiveHelpers.PostProcess.fst"
                     (Prims.of_int (457)) (Prims.of_int (16))
                     (Prims.of_int (459)) (Prims.of_int (50)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range
                     "FStar.InteractiveHelpers.PostProcess.fst"
                     (Prims.of_int (457)) (Prims.of_int (2))
                     (Prims.of_int (459)) (Prims.of_int (50)))))
            (Obj.magic uu___1)
            (fun uu___2 ->
               (fun uu___2 ->
                  Obj.magic
                    (FStar_InteractiveHelpers_Base.print_dbg dbg uu___2))
                 uu___2) in
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range
                   "FStar.InteractiveHelpers.PostProcess.fst"
                   (Prims.of_int (457)) (Prims.of_int (2))
                   (Prims.of_int (459)) (Prims.of_int (50)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range
                   "FStar.InteractiveHelpers.PostProcess.fst"
                   (Prims.of_int (459)) (Prims.of_int (51))
                   (Prims.of_int (462)) (Prims.of_int (49)))))
          (Obj.magic uu___)
          (fun uu___1 ->
             (fun uu___1 ->
                let uu___2 = split_conjunctions p in
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "FStar.InteractiveHelpers.PostProcess.fst"
                              (Prims.of_int (460)) (Prims.of_int (18))
                              (Prims.of_int (460)) (Prims.of_int (38)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "FStar.InteractiveHelpers.PostProcess.fst"
                              (Prims.of_int (461)) (Prims.of_int (2))
                              (Prims.of_int (462)) (Prims.of_int (49)))))
                     (Obj.magic uu___2)
                     (fun uu___3 ->
                        (fun conjuncts ->
                           let uu___3 =
                             let uu___4 =
                               let uu___5 =
                                 FStar_InteractiveHelpers_Base.list_to_string
                                   FStarC_Tactics_V1_Builtins.term_to_string
                                   conjuncts in
                               FStar_Tactics_Effect.tac_bind
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "FStar.InteractiveHelpers.PostProcess.fst"
                                          (Prims.of_int (461))
                                          (Prims.of_int (34))
                                          (Prims.of_int (461))
                                          (Prims.of_int (73)))))
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
                                      (fun uu___7 ->
                                         Prims.strcat "Conjuncts:\n" uu___6)) in
                             FStar_Tactics_Effect.tac_bind
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "FStar.InteractiveHelpers.PostProcess.fst"
                                        (Prims.of_int (461))
                                        (Prims.of_int (16))
                                        (Prims.of_int (461))
                                        (Prims.of_int (74)))))
                               (FStar_Sealed.seal
                                  (Obj.magic
                                     (FStar_Range.mk_range
                                        "FStar.InteractiveHelpers.PostProcess.fst"
                                        (Prims.of_int (461))
                                        (Prims.of_int (2))
                                        (Prims.of_int (461))
                                        (Prims.of_int (74)))))
                               (Obj.magic uu___4)
                               (fun uu___5 ->
                                  (fun uu___5 ->
                                     Obj.magic
                                       (FStar_InteractiveHelpers_Base.print_dbg
                                          dbg uu___5)) uu___5) in
                           Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "FStar.InteractiveHelpers.PostProcess.fst"
                                         (Prims.of_int (461))
                                         (Prims.of_int (2))
                                         (Prims.of_int (461))
                                         (Prims.of_int (74)))))
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "FStar.InteractiveHelpers.PostProcess.fst"
                                         (Prims.of_int (462))
                                         (Prims.of_int (2))
                                         (Prims.of_int (462))
                                         (Prims.of_int (49)))))
                                (Obj.magic uu___3)
                                (fun uu___4 ->
                                   (fun uu___4 ->
                                      Obj.magic
                                        (FStar_Tactics_Util.tryPick
                                           (is_equality_for_term dbg tm)
                                           conjuncts)) uu___4))) uu___3)))
               uu___1)
let (find_equality_from_post :
  Prims.bool ->
    FStar_InteractiveHelpers_Base.genv ->
      FStarC_Reflection_Types.term ->
        FStarC_Reflection_Types.bv ->
          FStarC_Reflection_Types.typ ->
            FStarC_Reflection_Types.term ->
              FStar_InteractiveHelpers_Effectful.effect_info ->
                FStarC_Reflection_V1_Data.term_view Prims.list ->
                  FStarC_Reflection_V1_Data.term_view Prims.list ->
                    ((FStar_InteractiveHelpers_Base.genv *
                       FStarC_Reflection_Types.term
                       FStar_Pervasives_Native.option),
                      unit) FStar_Tactics_Effect.tac_repr)
  =
  fun dbg ->
    fun ge0 ->
      fun tm ->
        fun let_bv ->
          fun let_bvty ->
            fun ret_value ->
              fun einfo ->
                fun parents ->
                  fun children ->
                    let uu___ =
                      FStar_InteractiveHelpers_Base.print_dbg dbg
                        "[> find_equality_from_post" in
                    FStar_Tactics_Effect.tac_bind
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range
                               "FStar.InteractiveHelpers.PostProcess.fst"
                               (Prims.of_int (469)) (Prims.of_int (2))
                               (Prims.of_int (469)) (Prims.of_int (44)))))
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range
                               "FStar.InteractiveHelpers.PostProcess.fst"
                               (Prims.of_int (469)) (Prims.of_int (45))
                               (Prims.of_int (487)) (Prims.of_int (27)))))
                      (Obj.magic uu___)
                      (fun uu___1 ->
                         (fun uu___1 ->
                            let uu___2 =
                              FStar_InteractiveHelpers_ExploreTerm.get_type_info_from_type
                                let_bvty in
                            Obj.magic
                              (FStar_Tactics_Effect.tac_bind
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "FStar.InteractiveHelpers.PostProcess.fst"
                                          (Prims.of_int (470))
                                          (Prims.of_int (14))
                                          (Prims.of_int (470))
                                          (Prims.of_int (46)))))
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "FStar.InteractiveHelpers.PostProcess.fst"
                                          (Prims.of_int (470))
                                          (Prims.of_int (49))
                                          (Prims.of_int (487))
                                          (Prims.of_int (27)))))
                                 (Obj.magic uu___2)
                                 (fun uu___3 ->
                                    (fun tinfo ->
                                       let uu___3 =
                                         FStar_InteractiveHelpers_Effectful.pre_post_to_propositions
                                           dbg ge0
                                           einfo.FStar_InteractiveHelpers_Effectful.ei_type
                                           ret_value
                                           (FStar_Pervasives_Native.Some
                                              (FStar_Reflection_V1_Derived.mk_binder
                                                 let_bv let_bvty)) tinfo
                                           einfo.FStar_InteractiveHelpers_Effectful.ei_pre
                                           einfo.FStar_InteractiveHelpers_Effectful.ei_post
                                           parents children in
                                       Obj.magic
                                         (FStar_Tactics_Effect.tac_bind
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "FStar.InteractiveHelpers.PostProcess.fst"
                                                     (Prims.of_int (473))
                                                     (Prims.of_int (4))
                                                     (Prims.of_int (474))
                                                     (Prims.of_int (78)))))
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "FStar.InteractiveHelpers.PostProcess.fst"
                                                     (Prims.of_int (470))
                                                     (Prims.of_int (49))
                                                     (Prims.of_int (487))
                                                     (Prims.of_int (27)))))
                                            (Obj.magic uu___3)
                                            (fun uu___4 ->
                                               (fun uu___4 ->
                                                  match uu___4 with
                                                  | (ge1, uu___5, post_prop)
                                                      ->
                                                      let uu___6 =
                                                        let uu___7 =
                                                          let uu___8 =
                                                            FStar_InteractiveHelpers_Base.option_to_string
                                                              FStarC_Tactics_V1_Builtins.term_to_string
                                                              post_prop in
                                                          FStar_Tactics_Effect.tac_bind
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (476))
                                                                    (Prims.of_int (37))
                                                                    (Prims.of_int (476))
                                                                    (Prims.of_int (78)))))
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
                                                                 (fun uu___10
                                                                    ->
                                                                    Prims.strcat
                                                                    "Computed post: "
                                                                    uu___9)) in
                                                        FStar_Tactics_Effect.tac_bind
                                                          (FStar_Sealed.seal
                                                             (Obj.magic
                                                                (FStar_Range.mk_range
                                                                   "FStar.InteractiveHelpers.PostProcess.fst"
                                                                   (Prims.of_int (476))
                                                                   (Prims.of_int (16))
                                                                   (Prims.of_int (476))
                                                                   (Prims.of_int (79)))))
                                                          (FStar_Sealed.seal
                                                             (Obj.magic
                                                                (FStar_Range.mk_range
                                                                   "FStar.InteractiveHelpers.PostProcess.fst"
                                                                   (Prims.of_int (476))
                                                                   (Prims.of_int (2))
                                                                   (Prims.of_int (476))
                                                                   (Prims.of_int (79)))))
                                                          (Obj.magic uu___7)
                                                          (fun uu___8 ->
                                                             (fun uu___8 ->
                                                                Obj.magic
                                                                  (FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    uu___8))
                                                               uu___8) in
                                                      Obj.magic
                                                        (FStar_Tactics_Effect.tac_bind
                                                           (FStar_Sealed.seal
                                                              (Obj.magic
                                                                 (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (476))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (476))
                                                                    (Prims.of_int (79)))))
                                                           (FStar_Sealed.seal
                                                              (Obj.magic
                                                                 (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (476))
                                                                    (Prims.of_int (80))
                                                                    (Prims.of_int (487))
                                                                    (Prims.of_int (27)))))
                                                           (Obj.magic uu___6)
                                                           (fun uu___7 ->
                                                              (fun uu___7 ->
                                                                 let uu___8 =
                                                                   match post_prop
                                                                   with
                                                                   | 
                                                                   FStar_Pervasives_Native.None
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    FStar_Pervasives_Native.None)))
                                                                   | 
                                                                   FStar_Pervasives_Native.Some
                                                                    p ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (find_subequality
                                                                    dbg tm p)) in
                                                                 Obj.magic
                                                                   (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (479))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (481))
                                                                    (Prims.of_int (41)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (485))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (487))
                                                                    (Prims.of_int (27)))))
                                                                    (Obj.magic
                                                                    uu___8)
                                                                    (fun res
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    match res
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    (ge0,
                                                                    FStar_Pervasives_Native.None)
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    tm1 ->
                                                                    (ge1,
                                                                    (FStar_Pervasives_Native.Some
                                                                    tm1))))))
                                                                uu___7)))
                                                 uu___4))) uu___3))) uu___1)
let rec (find_context_equality_aux :
  Prims.bool ->
    FStar_InteractiveHelpers_Base.genv ->
      FStarC_Reflection_Types.term ->
        FStarC_Reflection_Types.bv FStar_Pervasives_Native.option ->
          FStarC_Reflection_V1_Data.term_view Prims.list ->
            FStarC_Reflection_V1_Data.term_view Prims.list ->
              ((FStar_InteractiveHelpers_Base.genv *
                 FStarC_Reflection_Types.term FStar_Pervasives_Native.option),
                unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___5 ->
    fun uu___4 ->
      fun uu___3 ->
        fun uu___2 ->
          fun uu___1 ->
            fun uu___ ->
              (fun dbg ->
                 fun ge0 ->
                   fun tm ->
                     fun opt_bv ->
                       fun parents ->
                         fun children ->
                           match parents with
                           | [] ->
                               Obj.magic
                                 (Obj.repr
                                    (FStar_Tactics_Effect.lift_div_tac
                                       (fun uu___ ->
                                          (ge0, FStar_Pervasives_Native.None))))
                           | tv::parents' ->
                               Obj.magic
                                 (Obj.repr
                                    (let uu___ =
                                       let uu___1 =
                                         let uu___2 =
                                           let uu___3 =
                                             let uu___4 =
                                               FStarC_Tactics_V1_Builtins.term_to_string
                                                 tm in
                                             FStar_Tactics_Effect.tac_bind
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "FStar.InteractiveHelpers.PostProcess.fst"
                                                        (Prims.of_int (507))
                                                        (Prims.of_int (34))
                                                        (Prims.of_int (507))
                                                        (Prims.of_int (51)))))
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "FStar.InteractiveHelpers.PostProcess.fst"
                                                        (Prims.of_int (507))
                                                        (Prims.of_int (34))
                                                        (Prims.of_int (508))
                                                        (Prims.of_int (51)))))
                                               (Obj.magic uu___4)
                                               (fun uu___5 ->
                                                  (fun uu___5 ->
                                                     let uu___6 =
                                                       let uu___7 =
                                                         let uu___8 =
                                                           let uu___9 =
                                                             FStarC_Tactics_V1_Builtins.pack
                                                               tv in
                                                           FStar_Tactics_Effect.tac_bind
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (505))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (505))
                                                                    (Prims.of_int (6)))))
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (508))
                                                                    (Prims.of_int (34))
                                                                    (Prims.of_int (508))
                                                                    (Prims.of_int (51)))))
                                                             (Obj.magic
                                                                uu___9)
                                                             (fun uu___10 ->
                                                                (fun uu___10
                                                                   ->
                                                                   Obj.magic
                                                                    (FStarC_Tactics_V1_Builtins.term_to_string
                                                                    uu___10))
                                                                  uu___10) in
                                                         FStar_Tactics_Effect.tac_bind
                                                           (FStar_Sealed.seal
                                                              (Obj.magic
                                                                 (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (508))
                                                                    (Prims.of_int (34))
                                                                    (Prims.of_int (508))
                                                                    (Prims.of_int (51)))))
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
                                                                (fun uu___10
                                                                   ->
                                                                   Prims.strcat
                                                                    "- parent: "
                                                                    uu___9)) in
                                                       FStar_Tactics_Effect.tac_bind
                                                         (FStar_Sealed.seal
                                                            (Obj.magic
                                                               (FStar_Range.mk_range
                                                                  "FStar.InteractiveHelpers.PostProcess.fst"
                                                                  (Prims.of_int (508))
                                                                  (Prims.of_int (19))
                                                                  (Prims.of_int (508))
                                                                  (Prims.of_int (51)))))
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
                                                                   "\n"
                                                                   uu___8)) in
                                                     Obj.magic
                                                       (FStar_Tactics_Effect.tac_bind
                                                          (FStar_Sealed.seal
                                                             (Obj.magic
                                                                (FStar_Range.mk_range
                                                                   "FStar.InteractiveHelpers.PostProcess.fst"
                                                                   (Prims.of_int (507))
                                                                   (Prims.of_int (54))
                                                                   (Prims.of_int (508))
                                                                   (Prims.of_int (51)))))
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
                                                                    uu___5
                                                                    uu___7))))
                                                    uu___5) in
                                           FStar_Tactics_Effect.tac_bind
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "FStar.InteractiveHelpers.PostProcess.fst"
                                                      (Prims.of_int (507))
                                                      (Prims.of_int (34))
                                                      (Prims.of_int (508))
                                                      (Prims.of_int (51)))))
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "Prims.fst"
                                                      (Prims.of_int (611))
                                                      (Prims.of_int (19))
                                                      (Prims.of_int (611))
                                                      (Prims.of_int (31)))))
                                             (Obj.magic uu___3)
                                             (fun uu___4 ->
                                                FStar_Tactics_Effect.lift_div_tac
                                                  (fun uu___5 ->
                                                     Prims.strcat
                                                       "- term  : " uu___4)) in
                                         FStar_Tactics_Effect.tac_bind
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                    (Prims.of_int (507))
                                                    (Prims.of_int (19))
                                                    (Prims.of_int (508))
                                                    (Prims.of_int (51)))))
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "Prims.fst"
                                                    (Prims.of_int (611))
                                                    (Prims.of_int (19))
                                                    (Prims.of_int (611))
                                                    (Prims.of_int (31)))))
                                           (Obj.magic uu___2)
                                           (fun uu___3 ->
                                              FStar_Tactics_Effect.lift_div_tac
                                                (fun uu___4 ->
                                                   Prims.strcat
                                                     "[> find_context_equality:\n"
                                                     uu___3)) in
                                       FStar_Tactics_Effect.tac_bind
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "FStar.InteractiveHelpers.PostProcess.fst"
                                                  (Prims.of_int (506))
                                                  (Prims.of_int (18))
                                                  (Prims.of_int (508))
                                                  (Prims.of_int (52)))))
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "FStar.InteractiveHelpers.PostProcess.fst"
                                                  (Prims.of_int (506))
                                                  (Prims.of_int (4))
                                                  (Prims.of_int (508))
                                                  (Prims.of_int (52)))))
                                         (Obj.magic uu___1)
                                         (fun uu___2 ->
                                            (fun uu___2 ->
                                               Obj.magic
                                                 (FStar_InteractiveHelpers_Base.print_dbg
                                                    dbg uu___2)) uu___2) in
                                     FStar_Tactics_Effect.tac_bind
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "FStar.InteractiveHelpers.PostProcess.fst"
                                                (Prims.of_int (506))
                                                (Prims.of_int (4))
                                                (Prims.of_int (508))
                                                (Prims.of_int (52)))))
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "FStar.InteractiveHelpers.PostProcess.fst"
                                                (Prims.of_int (510))
                                                (Prims.of_int (4))
                                                (Prims.of_int (533))
                                                (Prims.of_int (79)))))
                                       (Obj.magic uu___)
                                       (fun uu___1 ->
                                          (fun uu___1 ->
                                             match tv with
                                             | FStarC_Reflection_V1_Data.Tv_Let
                                                 (uu___2, uu___3, bv', ty,
                                                  def, uu___4)
                                                 ->
                                                 let uu___5 =
                                                   FStar_InteractiveHelpers_Base.print_dbg
                                                     dbg "Is Tv_Let" in
                                                 Obj.magic
                                                   (FStar_Tactics_Effect.tac_bind
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "FStar.InteractiveHelpers.PostProcess.fst"
                                                               (Prims.of_int (512))
                                                               (Prims.of_int (6))
                                                               (Prims.of_int (512))
                                                               (Prims.of_int (31)))))
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "FStar.InteractiveHelpers.PostProcess.fst"
                                                               (Prims.of_int (512))
                                                               (Prims.of_int (32))
                                                               (Prims.of_int (532))
                                                               (Prims.of_int (11)))))
                                                      (Obj.magic uu___5)
                                                      (fun uu___6 ->
                                                         (fun uu___6 ->
                                                            let uu___7 =
                                                              FStar_InteractiveHelpers_Effectful.compute_eterm_info
                                                                dbg
                                                                ge0.FStar_InteractiveHelpers_Base.env
                                                                def in
                                                            Obj.magic
                                                              (FStar_Tactics_Effect.tac_bind
                                                                 (FStar_Sealed.seal
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (513))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (513))
                                                                    (Prims.of_int (54)))))
                                                                 (FStar_Sealed.seal
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (513))
                                                                    (Prims.of_int (57))
                                                                    (Prims.of_int (532))
                                                                    (Prims.of_int (11)))))
                                                                 (Obj.magic
                                                                    uu___7)
                                                                 (fun uu___8
                                                                    ->
                                                                    (fun
                                                                    tm_info
                                                                    ->
                                                                    let uu___8
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    tm_info.FStar_InteractiveHelpers_Effectful.einfo)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (514))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (514))
                                                                    (Prims.of_int (31)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (514))
                                                                    (Prims.of_int (34))
                                                                    (Prims.of_int (532))
                                                                    (Prims.of_int (11)))))
                                                                    (Obj.magic
                                                                    uu___8)
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun
                                                                    einfo ->
                                                                    let uu___9
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    match opt_bv
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    tm_bv ->
                                                                    FStar_InteractiveHelpers_Base.bv_eq
                                                                    tm_bv bv'
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    -> false)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (521))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (523))
                                                                    (Prims.of_int (23)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (525))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (532))
                                                                    (Prims.of_int (11)))))
                                                                    (Obj.magic
                                                                    uu___9)
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun
                                                                    let_bv_is_tm
                                                                    ->
                                                                    if
                                                                    let_bv_is_tm
                                                                    &&
                                                                    (FStar_InteractiveHelpers_ExploreTerm.effect_type_is_pure
                                                                    einfo.FStar_InteractiveHelpers_Effectful.ei_type)
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (ge0,
                                                                    (FStar_Pervasives_Native.Some
                                                                    def)))))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (let uu___11
                                                                    =
                                                                    FStarC_Tactics_V1_Builtins.pack
                                                                    (FStarC_Reflection_V1_Data.Tv_Var
                                                                    bv') in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (527))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (527))
                                                                    (Prims.of_int (41)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (528))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (531))
                                                                    (Prims.of_int (90)))))
                                                                    (Obj.magic
                                                                    uu___11)
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    (fun
                                                                    ret_value
                                                                    ->
                                                                    let uu___12
                                                                    =
                                                                    find_equality_from_post
                                                                    dbg ge0
                                                                    tm bv' ty
                                                                    ret_value
                                                                    einfo
                                                                    parents
                                                                    children in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (528))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (529))
                                                                    (Prims.of_int (66)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (528))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (531))
                                                                    (Prims.of_int (90)))))
                                                                    (Obj.magic
                                                                    uu___12)
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    match uu___13
                                                                    with
                                                                    | 
                                                                    (ge1,
                                                                    FStar_Pervasives_Native.Some
                                                                    p) ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    (ge1,
                                                                    (FStar_Pervasives_Native.Some
                                                                    p)))))
                                                                    | 
                                                                    (uu___14,
                                                                    FStar_Pervasives_Native.None)
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (find_context_equality_aux
                                                                    dbg ge0
                                                                    tm opt_bv
                                                                    parents'
                                                                    (tv ::
                                                                    children))))
                                                                    uu___13)))
                                                                    uu___12))))
                                                                    uu___10)))
                                                                    uu___9)))
                                                                    uu___8)))
                                                           uu___6))
                                             | uu___2 ->
                                                 Obj.magic
                                                   (find_context_equality_aux
                                                      dbg ge0 tm opt_bv
                                                      parents' (tv ::
                                                      children))) uu___1))))
                uu___5 uu___4 uu___3 uu___2 uu___1 uu___
let (find_context_equality :
  Prims.bool ->
    FStar_InteractiveHelpers_Base.genv ->
      FStarC_Reflection_Types.term ->
        FStarC_Reflection_V1_Data.term_view Prims.list ->
          FStarC_Reflection_V1_Data.term_view Prims.list ->
            ((FStar_InteractiveHelpers_Base.genv *
               FStarC_Reflection_Types.term FStar_Pervasives_Native.option),
              unit) FStar_Tactics_Effect.tac_repr)
  =
  fun dbg ->
    fun ge0 ->
      fun tm ->
        fun parents ->
          fun children ->
            let uu___ =
              let uu___1 = FStarC_Tactics_V1_Builtins.inspect tm in
              FStar_Tactics_Effect.tac_bind
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range
                         "FStar.InteractiveHelpers.PostProcess.fst"
                         (Prims.of_int (537)) (Prims.of_int (10))
                         (Prims.of_int (537)) (Prims.of_int (20)))))
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range
                         "FStar.InteractiveHelpers.PostProcess.fst"
                         (Prims.of_int (537)) (Prims.of_int (4))
                         (Prims.of_int (539)) (Prims.of_int (15)))))
                (Obj.magic uu___1)
                (fun uu___2 ->
                   FStar_Tactics_Effect.lift_div_tac
                     (fun uu___3 ->
                        match uu___2 with
                        | FStarC_Reflection_V1_Data.Tv_Var bv ->
                            FStar_Pervasives_Native.Some bv
                        | uu___4 -> FStar_Pervasives_Native.None)) in
            FStar_Tactics_Effect.tac_bind
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range
                       "FStar.InteractiveHelpers.PostProcess.fst"
                       (Prims.of_int (537)) (Prims.of_int (4))
                       (Prims.of_int (539)) (Prims.of_int (15)))))
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range
                       "FStar.InteractiveHelpers.PostProcess.fst"
                       (Prims.of_int (541)) (Prims.of_int (2))
                       (Prims.of_int (541)) (Prims.of_int (62)))))
              (Obj.magic uu___)
              (fun uu___1 ->
                 (fun opt_bv ->
                    Obj.magic
                      (find_context_equality_aux dbg ge0 tm opt_bv parents
                         children)) uu___1)
let rec (replace_term_in :
  Prims.bool ->
    FStarC_Reflection_Types.term ->
      FStarC_Reflection_Types.term ->
        FStarC_Reflection_Types.term ->
          (FStarC_Reflection_Types.term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___3 ->
    fun uu___2 ->
      fun uu___1 ->
        fun uu___ ->
          (fun dbg ->
             fun from_term ->
               fun to_term ->
                 fun tm ->
                   if FStar_InteractiveHelpers_Effectful.term_eq from_term tm
                   then
                     Obj.magic
                       (Obj.repr
                          (FStar_Tactics_Effect.lift_div_tac
                             (fun uu___ -> to_term)))
                   else
                     Obj.magic
                       (Obj.repr
                          (let uu___1 = FStarC_Tactics_V1_Builtins.inspect tm in
                           FStar_Tactics_Effect.tac_bind
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "FStar.InteractiveHelpers.PostProcess.fst"
                                      (Prims.of_int (547)) (Prims.of_int (8))
                                      (Prims.of_int (547))
                                      (Prims.of_int (18)))))
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "FStar.InteractiveHelpers.PostProcess.fst"
                                      (Prims.of_int (547)) (Prims.of_int (2))
                                      (Prims.of_int (590)) (Prims.of_int (6)))))
                             (Obj.magic uu___1)
                             (fun uu___2 ->
                                (fun uu___2 ->
                                   match uu___2 with
                                   | FStarC_Reflection_V1_Data.Tv_Var uu___3
                                       ->
                                       Obj.magic
                                         (Obj.repr
                                            (FStar_Tactics_Effect.lift_div_tac
                                               (fun uu___4 -> tm)))
                                   | FStarC_Reflection_V1_Data.Tv_BVar uu___3
                                       ->
                                       Obj.magic
                                         (Obj.repr
                                            (FStar_Tactics_Effect.lift_div_tac
                                               (fun uu___4 -> tm)))
                                   | FStarC_Reflection_V1_Data.Tv_FVar uu___3
                                       ->
                                       Obj.magic
                                         (Obj.repr
                                            (FStar_Tactics_Effect.lift_div_tac
                                               (fun uu___4 -> tm)))
                                   | FStarC_Reflection_V1_Data.Tv_App
                                       (hd, (a, qual)) ->
                                       Obj.magic
                                         (Obj.repr
                                            (let uu___3 =
                                               replace_term_in dbg from_term
                                                 to_term a in
                                             FStar_Tactics_Effect.tac_bind
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "FStar.InteractiveHelpers.PostProcess.fst"
                                                        (Prims.of_int (550))
                                                        (Prims.of_int (13))
                                                        (Prims.of_int (550))
                                                        (Prims.of_int (52)))))
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "FStar.InteractiveHelpers.PostProcess.fst"
                                                        (Prims.of_int (550))
                                                        (Prims.of_int (55))
                                                        (Prims.of_int (552))
                                                        (Prims.of_int (32)))))
                                               (Obj.magic uu___3)
                                               (fun uu___4 ->
                                                  (fun a' ->
                                                     let uu___4 =
                                                       replace_term_in dbg
                                                         from_term to_term hd in
                                                     Obj.magic
                                                       (FStar_Tactics_Effect.tac_bind
                                                          (FStar_Sealed.seal
                                                             (Obj.magic
                                                                (FStar_Range.mk_range
                                                                   "FStar.InteractiveHelpers.PostProcess.fst"
                                                                   (Prims.of_int (551))
                                                                   (Prims.of_int (14))
                                                                   (Prims.of_int (551))
                                                                   (Prims.of_int (54)))))
                                                          (FStar_Sealed.seal
                                                             (Obj.magic
                                                                (FStar_Range.mk_range
                                                                   "FStar.InteractiveHelpers.PostProcess.fst"
                                                                   (Prims.of_int (552))
                                                                   (Prims.of_int (4))
                                                                   (Prims.of_int (552))
                                                                   (Prims.of_int (32)))))
                                                          (Obj.magic uu___4)
                                                          (fun uu___5 ->
                                                             (fun hd' ->
                                                                Obj.magic
                                                                  (FStarC_Tactics_V1_Builtins.pack
                                                                    (FStarC_Reflection_V1_Data.Tv_App
                                                                    (hd',
                                                                    (a',
                                                                    qual)))))
                                                               uu___5)))
                                                    uu___4)))
                                   | FStarC_Reflection_V1_Data.Tv_Abs
                                       (br, body) ->
                                       Obj.magic
                                         (Obj.repr
                                            (let uu___3 =
                                               replace_term_in dbg from_term
                                                 to_term body in
                                             FStar_Tactics_Effect.tac_bind
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "FStar.InteractiveHelpers.PostProcess.fst"
                                                        (Prims.of_int (554))
                                                        (Prims.of_int (16))
                                                        (Prims.of_int (554))
                                                        (Prims.of_int (58)))))
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "FStar.InteractiveHelpers.PostProcess.fst"
                                                        (Prims.of_int (555))
                                                        (Prims.of_int (4))
                                                        (Prims.of_int (555))
                                                        (Prims.of_int (26)))))
                                               (Obj.magic uu___3)
                                               (fun uu___4 ->
                                                  (fun body' ->
                                                     Obj.magic
                                                       (FStarC_Tactics_V1_Builtins.pack
                                                          (FStarC_Reflection_V1_Data.Tv_Abs
                                                             (br, body'))))
                                                    uu___4)))
                                   | FStarC_Reflection_V1_Data.Tv_Arrow
                                       (br, c0) ->
                                       Obj.magic
                                         (Obj.repr
                                            (FStar_Tactics_Effect.lift_div_tac
                                               (fun uu___3 -> tm)))
                                   | FStarC_Reflection_V1_Data.Tv_Type uu___3
                                       ->
                                       Obj.magic
                                         (Obj.repr
                                            (FStar_Tactics_Effect.lift_div_tac
                                               (fun uu___4 -> tm)))
                                   | FStarC_Reflection_V1_Data.Tv_Refine
                                       (bv, sort, ref) ->
                                       Obj.magic
                                         (Obj.repr
                                            (let uu___3 =
                                               replace_term_in dbg from_term
                                                 to_term sort in
                                             FStar_Tactics_Effect.tac_bind
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "FStar.InteractiveHelpers.PostProcess.fst"
                                                        (Prims.of_int (559))
                                                        (Prims.of_int (16))
                                                        (Prims.of_int (559))
                                                        (Prims.of_int (58)))))
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "FStar.InteractiveHelpers.PostProcess.fst"
                                                        (Prims.of_int (559))
                                                        (Prims.of_int (61))
                                                        (Prims.of_int (561))
                                                        (Prims.of_int (34)))))
                                               (Obj.magic uu___3)
                                               (fun uu___4 ->
                                                  (fun sort' ->
                                                     let uu___4 =
                                                       replace_term_in dbg
                                                         from_term to_term
                                                         ref in
                                                     Obj.magic
                                                       (FStar_Tactics_Effect.tac_bind
                                                          (FStar_Sealed.seal
                                                             (Obj.magic
                                                                (FStar_Range.mk_range
                                                                   "FStar.InteractiveHelpers.PostProcess.fst"
                                                                   (Prims.of_int (560))
                                                                   (Prims.of_int (15))
                                                                   (Prims.of_int (560))
                                                                   (Prims.of_int (56)))))
                                                          (FStar_Sealed.seal
                                                             (Obj.magic
                                                                (FStar_Range.mk_range
                                                                   "FStar.InteractiveHelpers.PostProcess.fst"
                                                                   (Prims.of_int (561))
                                                                   (Prims.of_int (4))
                                                                   (Prims.of_int (561))
                                                                   (Prims.of_int (34)))))
                                                          (Obj.magic uu___4)
                                                          (fun uu___5 ->
                                                             (fun ref' ->
                                                                Obj.magic
                                                                  (FStarC_Tactics_V1_Builtins.pack
                                                                    (FStarC_Reflection_V1_Data.Tv_Refine
                                                                    (bv,
                                                                    sort',
                                                                    ref'))))
                                                               uu___5)))
                                                    uu___4)))
                                   | FStarC_Reflection_V1_Data.Tv_Const
                                       uu___3 ->
                                       Obj.magic
                                         (Obj.repr
                                            (FStar_Tactics_Effect.lift_div_tac
                                               (fun uu___4 -> tm)))
                                   | FStarC_Reflection_V1_Data.Tv_Uvar
                                       (uu___3, uu___4) ->
                                       Obj.magic
                                         (Obj.repr
                                            (FStar_Tactics_Effect.lift_div_tac
                                               (fun uu___5 -> tm)))
                                   | FStarC_Reflection_V1_Data.Tv_Let
                                       (recf, attrs, bv, ty, def, body) ->
                                       Obj.magic
                                         (Obj.repr
                                            (let uu___3 =
                                               replace_term_in dbg from_term
                                                 to_term def in
                                             FStar_Tactics_Effect.tac_bind
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "FStar.InteractiveHelpers.PostProcess.fst"
                                                        (Prims.of_int (567))
                                                        (Prims.of_int (15))
                                                        (Prims.of_int (567))
                                                        (Prims.of_int (56)))))
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "FStar.InteractiveHelpers.PostProcess.fst"
                                                        (Prims.of_int (567))
                                                        (Prims.of_int (59))
                                                        (Prims.of_int (569))
                                                        (Prims.of_int (45)))))
                                               (Obj.magic uu___3)
                                               (fun uu___4 ->
                                                  (fun def' ->
                                                     let uu___4 =
                                                       replace_term_in dbg
                                                         from_term to_term
                                                         body in
                                                     Obj.magic
                                                       (FStar_Tactics_Effect.tac_bind
                                                          (FStar_Sealed.seal
                                                             (Obj.magic
                                                                (FStar_Range.mk_range
                                                                   "FStar.InteractiveHelpers.PostProcess.fst"
                                                                   (Prims.of_int (568))
                                                                   (Prims.of_int (16))
                                                                   (Prims.of_int (568))
                                                                   (Prims.of_int (58)))))
                                                          (FStar_Sealed.seal
                                                             (Obj.magic
                                                                (FStar_Range.mk_range
                                                                   "FStar.InteractiveHelpers.PostProcess.fst"
                                                                   (Prims.of_int (569))
                                                                   (Prims.of_int (4))
                                                                   (Prims.of_int (569))
                                                                   (Prims.of_int (45)))))
                                                          (Obj.magic uu___4)
                                                          (fun uu___5 ->
                                                             (fun body' ->
                                                                Obj.magic
                                                                  (FStarC_Tactics_V1_Builtins.pack
                                                                    (FStarC_Reflection_V1_Data.Tv_Let
                                                                    (recf,
                                                                    attrs,
                                                                    bv, ty,
                                                                    def',
                                                                    body'))))
                                                               uu___5)))
                                                    uu___4)))
                                   | FStarC_Reflection_V1_Data.Tv_Match
                                       (scrutinee, ret_opt, branches) ->
                                       Obj.magic
                                         (Obj.repr
                                            (let uu___3 =
                                               Obj.magic
                                                 (FStar_Tactics_Effect.lift_div_tac
                                                    (fun uu___4 ->
                                                       fun br ->
                                                         let uu___5 =
                                                           Obj.magic
                                                             (FStar_Tactics_Effect.lift_div_tac
                                                                (fun uu___6
                                                                   -> br)) in
                                                         FStar_Tactics_Effect.tac_bind
                                                           (FStar_Sealed.seal
                                                              (Obj.magic
                                                                 (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (574))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (574))
                                                                    (Prims.of_int (24)))))
                                                           (FStar_Sealed.seal
                                                              (Obj.magic
                                                                 (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (572))
                                                                    (Prims.of_int (51))
                                                                    (Prims.of_int (576))
                                                                    (Prims.of_int (18)))))
                                                           (Obj.magic uu___5)
                                                           (fun uu___6 ->
                                                              (fun uu___6 ->
                                                                 match uu___6
                                                                 with
                                                                 | (pat,
                                                                    body) ->
                                                                    let uu___7
                                                                    =
                                                                    replace_term_in
                                                                    dbg
                                                                    from_term
                                                                    to_term
                                                                    body in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (575))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (575))
                                                                    (Prims.of_int (60)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (576))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (576))
                                                                    (Prims.of_int (18)))))
                                                                    (Obj.magic
                                                                    uu___7)
                                                                    (fun
                                                                    body' ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    (pat,
                                                                    body')))))
                                                                uu___6))) in
                                             FStar_Tactics_Effect.tac_bind
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "FStar.InteractiveHelpers.PostProcess.fst"
                                                        (Prims.of_int (572))
                                                        (Prims.of_int (51))
                                                        (Prims.of_int (576))
                                                        (Prims.of_int (18)))))
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "FStar.InteractiveHelpers.PostProcess.fst"
                                                        (Prims.of_int (577))
                                                        (Prims.of_int (6))
                                                        (Prims.of_int (580))
                                                        (Prims.of_int (48)))))
                                               (Obj.magic uu___3)
                                               (fun uu___4 ->
                                                  (fun explore_branch ->
                                                     let uu___4 =
                                                       replace_term_in dbg
                                                         from_term to_term
                                                         scrutinee in
                                                     Obj.magic
                                                       (FStar_Tactics_Effect.tac_bind
                                                          (FStar_Sealed.seal
                                                             (Obj.magic
                                                                (FStar_Range.mk_range
                                                                   "FStar.InteractiveHelpers.PostProcess.fst"
                                                                   (Prims.of_int (578))
                                                                   (Prims.of_int (21))
                                                                   (Prims.of_int (578))
                                                                   (Prims.of_int (68)))))
                                                          (FStar_Sealed.seal
                                                             (Obj.magic
                                                                (FStar_Range.mk_range
                                                                   "FStar.InteractiveHelpers.PostProcess.fst"
                                                                   (Prims.of_int (578))
                                                                   (Prims.of_int (71))
                                                                   (Prims.of_int (580))
                                                                   (Prims.of_int (48)))))
                                                          (Obj.magic uu___4)
                                                          (fun uu___5 ->
                                                             (fun scrutinee'
                                                                ->
                                                                let uu___5 =
                                                                  FStar_Tactics_Util.map
                                                                    explore_branch
                                                                    branches in
                                                                Obj.magic
                                                                  (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (579))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (579))
                                                                    (Prims.of_int (47)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (580))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (580))
                                                                    (Prims.of_int (48)))))
                                                                    (Obj.magic
                                                                    uu___5)
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    branches'
                                                                    ->
                                                                    Obj.magic
                                                                    (FStarC_Tactics_V1_Builtins.pack
                                                                    (FStarC_Reflection_V1_Data.Tv_Match
                                                                    (scrutinee',
                                                                    ret_opt,
                                                                    branches'))))
                                                                    uu___6)))
                                                               uu___5)))
                                                    uu___4)))
                                   | FStarC_Reflection_V1_Data.Tv_AscribedT
                                       (e, ty, tac, use_eq) ->
                                       Obj.magic
                                         (Obj.repr
                                            (let uu___3 =
                                               replace_term_in dbg from_term
                                                 to_term e in
                                             FStar_Tactics_Effect.tac_bind
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "FStar.InteractiveHelpers.PostProcess.fst"
                                                        (Prims.of_int (582))
                                                        (Prims.of_int (13))
                                                        (Prims.of_int (582))
                                                        (Prims.of_int (52)))))
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "FStar.InteractiveHelpers.PostProcess.fst"
                                                        (Prims.of_int (582))
                                                        (Prims.of_int (55))
                                                        (Prims.of_int (584))
                                                        (Prims.of_int (41)))))
                                               (Obj.magic uu___3)
                                               (fun uu___4 ->
                                                  (fun e' ->
                                                     let uu___4 =
                                                       replace_term_in dbg
                                                         from_term to_term ty in
                                                     Obj.magic
                                                       (FStar_Tactics_Effect.tac_bind
                                                          (FStar_Sealed.seal
                                                             (Obj.magic
                                                                (FStar_Range.mk_range
                                                                   "FStar.InteractiveHelpers.PostProcess.fst"
                                                                   (Prims.of_int (583))
                                                                   (Prims.of_int (14))
                                                                   (Prims.of_int (583))
                                                                   (Prims.of_int (54)))))
                                                          (FStar_Sealed.seal
                                                             (Obj.magic
                                                                (FStar_Range.mk_range
                                                                   "FStar.InteractiveHelpers.PostProcess.fst"
                                                                   (Prims.of_int (584))
                                                                   (Prims.of_int (4))
                                                                   (Prims.of_int (584))
                                                                   (Prims.of_int (41)))))
                                                          (Obj.magic uu___4)
                                                          (fun uu___5 ->
                                                             (fun ty' ->
                                                                Obj.magic
                                                                  (FStarC_Tactics_V1_Builtins.pack
                                                                    (FStarC_Reflection_V1_Data.Tv_AscribedT
                                                                    (e', ty',
                                                                    tac,
                                                                    use_eq))))
                                                               uu___5)))
                                                    uu___4)))
                                   | FStarC_Reflection_V1_Data.Tv_AscribedC
                                       (e, c, tac, use_eq) ->
                                       Obj.magic
                                         (Obj.repr
                                            (let uu___3 =
                                               replace_term_in dbg from_term
                                                 to_term e in
                                             FStar_Tactics_Effect.tac_bind
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "FStar.InteractiveHelpers.PostProcess.fst"
                                                        (Prims.of_int (586))
                                                        (Prims.of_int (13))
                                                        (Prims.of_int (586))
                                                        (Prims.of_int (52)))))
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "FStar.InteractiveHelpers.PostProcess.fst"
                                                        (Prims.of_int (587))
                                                        (Prims.of_int (4))
                                                        (Prims.of_int (587))
                                                        (Prims.of_int (39)))))
                                               (Obj.magic uu___3)
                                               (fun uu___4 ->
                                                  (fun e' ->
                                                     Obj.magic
                                                       (FStarC_Tactics_V1_Builtins.pack
                                                          (FStarC_Reflection_V1_Data.Tv_AscribedC
                                                             (e', c, tac,
                                                               use_eq))))
                                                    uu___4)))
                                   | uu___3 ->
                                       Obj.magic
                                         (Obj.repr
                                            (FStar_Tactics_Effect.lift_div_tac
                                               (fun uu___4 -> tm)))) uu___2))))
            uu___3 uu___2 uu___1 uu___
let rec (strip_implicit_parameters :
  FStarC_Reflection_Types.term ->
    (FStarC_Reflection_Types.term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun tm ->
    let uu___ = FStarC_Tactics_V1_Builtins.inspect tm in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.InteractiveHelpers.PostProcess.fst"
               (Prims.of_int (594)) (Prims.of_int (8)) (Prims.of_int (594))
               (Prims.of_int (18)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.InteractiveHelpers.PostProcess.fst"
               (Prims.of_int (594)) (Prims.of_int (2)) (Prims.of_int (597))
               (Prims.of_int (11))))) (Obj.magic uu___)
      (fun uu___1 ->
         (fun uu___1 ->
            match uu___1 with
            | FStarC_Reflection_V1_Data.Tv_App (hd, (a, qualif)) ->
                Obj.magic
                  (Obj.repr
                     (if FStarC_Reflection_V1_Data.uu___is_Q_Implicit qualif
                      then Obj.repr (strip_implicit_parameters hd)
                      else
                        Obj.repr
                          (FStar_Tactics_Effect.lift_div_tac
                             (fun uu___3 -> tm))))
            | uu___2 ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.lift_div_tac (fun uu___3 -> tm))))
           uu___1)
let (unfold_in_assert_or_assume :
  Prims.bool ->
    FStarC_Reflection_Types.term exploration_result ->
      (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun dbg ->
    fun ares ->
      let uu___ =
        let uu___1 =
          let uu___2 = FStarC_Tactics_V1_Builtins.term_to_string ares.res in
          FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range
                     "FStar.InteractiveHelpers.PostProcess.fst"
                     (Prims.of_int (601)) (Prims.of_int (54))
                     (Prims.of_int (601)) (Prims.of_int (77)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Prims.fst" (Prims.of_int (611))
                     (Prims.of_int (19)) (Prims.of_int (611))
                     (Prims.of_int (31))))) (Obj.magic uu___2)
            (fun uu___3 ->
               FStar_Tactics_Effect.lift_div_tac
                 (fun uu___4 ->
                    Prims.strcat "[> unfold_in_assert_or_assume:\n" uu___3)) in
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range
                   "FStar.InteractiveHelpers.PostProcess.fst"
                   (Prims.of_int (601)) (Prims.of_int (16))
                   (Prims.of_int (601)) (Prims.of_int (78)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range
                   "FStar.InteractiveHelpers.PostProcess.fst"
                   (Prims.of_int (601)) (Prims.of_int (2))
                   (Prims.of_int (601)) (Prims.of_int (78)))))
          (Obj.magic uu___1)
          (fun uu___2 ->
             (fun uu___2 ->
                Obj.magic
                  (FStar_InteractiveHelpers_Base.print_dbg dbg uu___2))
               uu___2) in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range
                 "FStar.InteractiveHelpers.PostProcess.fst"
                 (Prims.of_int (601)) (Prims.of_int (2)) (Prims.of_int (601))
                 (Prims.of_int (78)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range
                 "FStar.InteractiveHelpers.PostProcess.fst"
                 (Prims.of_int (601)) (Prims.of_int (79))
                 (Prims.of_int (735)) (Prims.of_int (30)))))
        (Obj.magic uu___)
        (fun uu___1 ->
           (fun uu___1 ->
              let uu___2 =
                Obj.magic
                  (FStar_Tactics_Effect.lift_div_tac
                     (fun uu___3 ->
                        fun t ->
                          find_focused_term dbg false ares.ge ares.parents
                            ares.tgt_comp t)) in
              Obj.magic
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range
                            "FStar.InteractiveHelpers.PostProcess.fst"
                            (Prims.of_int (605)) (Prims.of_int (4))
                            (Prims.of_int (605)) (Prims.of_int (68)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range
                            "FStar.InteractiveHelpers.PostProcess.fst"
                            (Prims.of_int (606)) (Prims.of_int (4))
                            (Prims.of_int (735)) (Prims.of_int (30)))))
                   (Obj.magic uu___2)
                   (fun uu___3 ->
                      (fun find_focused_in_term ->
                         let uu___3 =
                           Obj.magic
                             (FStar_Tactics_Effect.lift_div_tac
                                (fun uu___4 ->
                                   fun uu___5 ->
                                     let uu___6 =
                                       find_focused_in_term ares.res in
                                     FStar_Tactics_Effect.tac_bind
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "FStar.InteractiveHelpers.PostProcess.fst"
                                                (Prims.of_int (608))
                                                (Prims.of_int (10))
                                                (Prims.of_int (608))
                                                (Prims.of_int (39)))))
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "FStar.InteractiveHelpers.PostProcess.fst"
                                                (Prims.of_int (608))
                                                (Prims.of_int (4))
                                                (Prims.of_int (611))
                                                (Prims.of_int (93)))))
                                       (Obj.magic uu___6)
                                       (fun uu___7 ->
                                          (fun uu___7 ->
                                             match uu___7 with
                                             | FStar_Pervasives_Native.Some
                                                 res ->
                                                 Obj.magic
                                                   (Obj.repr
                                                      (FStar_Tactics_Effect.lift_div_tac
                                                         (fun uu___8 ->
                                                            ((ares.res), res,
                                                              (fun uu___9 ->
                                                                 (fun x ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    x)))
                                                                   uu___9),
                                                              true))))
                                             | FStar_Pervasives_Native.None
                                                 ->
                                                 Obj.magic
                                                   (Obj.repr
                                                      (FStar_InteractiveHelpers_Base.mfail
                                                         "unfold_in_assert_or_assume: could not find a focused term in the assert")))
                                            uu___7))) in
                         Obj.magic
                           (FStar_Tactics_Effect.tac_bind
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "FStar.InteractiveHelpers.PostProcess.fst"
                                       (Prims.of_int (608))
                                       (Prims.of_int (4))
                                       (Prims.of_int (611))
                                       (Prims.of_int (93)))))
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "FStar.InteractiveHelpers.PostProcess.fst"
                                       (Prims.of_int (612))
                                       (Prims.of_int (4))
                                       (Prims.of_int (735))
                                       (Prims.of_int (30)))))
                              (Obj.magic uu___3)
                              (fun uu___4 ->
                                 (fun find_in_whole_term ->
                                    let uu___4 =
                                      let uu___5 =
                                        let uu___6 =
                                          let uu___7 =
                                            FStarC_Tactics_V1_Builtins.term_to_string
                                              ares.res in
                                          FStar_Tactics_Effect.tac_bind
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "FStar.InteractiveHelpers.PostProcess.fst"
                                                     (Prims.of_int (622))
                                                     (Prims.of_int (43))
                                                     (Prims.of_int (622))
                                                     (Prims.of_int (66)))))
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
                                                      "Assertion: " uu___8)) in
                                        FStar_Tactics_Effect.tac_bind
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "FStar.InteractiveHelpers.PostProcess.fst"
                                                   (Prims.of_int (622))
                                                   (Prims.of_int (26))
                                                   (Prims.of_int (622))
                                                   (Prims.of_int (67)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "FStar.InteractiveHelpers.PostProcess.fst"
                                                   (Prims.of_int (622))
                                                   (Prims.of_int (12))
                                                   (Prims.of_int (622))
                                                   (Prims.of_int (67)))))
                                          (Obj.magic uu___6)
                                          (fun uu___7 ->
                                             (fun uu___7 ->
                                                Obj.magic
                                                  (FStar_InteractiveHelpers_Base.print_dbg
                                                     dbg uu___7)) uu___7) in
                                      FStar_Tactics_Effect.tac_bind
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "FStar.InteractiveHelpers.PostProcess.fst"
                                                 (Prims.of_int (622))
                                                 (Prims.of_int (12))
                                                 (Prims.of_int (622))
                                                 (Prims.of_int (67)))))
                                        (FStar_Sealed.seal
                                           (Obj.magic
                                              (FStar_Range.mk_range
                                                 "FStar.InteractiveHelpers.PostProcess.fst"
                                                 (Prims.of_int (623))
                                                 (Prims.of_int (4))
                                                 (Prims.of_int (649))
                                                 (Prims.of_int (27)))))
                                        (Obj.magic uu___5)
                                        (fun uu___6 ->
                                           (fun uu___6 ->
                                              let uu___7 = is_eq dbg ares.res in
                                              Obj.magic
                                                (FStar_Tactics_Effect.tac_bind
                                                   (FStar_Sealed.seal
                                                      (Obj.magic
                                                         (FStar_Range.mk_range
                                                            "FStar.InteractiveHelpers.PostProcess.fst"
                                                            (Prims.of_int (623))
                                                            (Prims.of_int (10))
                                                            (Prims.of_int (623))
                                                            (Prims.of_int (28)))))
                                                   (FStar_Sealed.seal
                                                      (Obj.magic
                                                         (FStar_Range.mk_range
                                                            "FStar.InteractiveHelpers.PostProcess.fst"
                                                            (Prims.of_int (623))
                                                            (Prims.of_int (4))
                                                            (Prims.of_int (649))
                                                            (Prims.of_int (27)))))
                                                   (Obj.magic uu___7)
                                                   (fun uu___8 ->
                                                      (fun uu___8 ->
                                                         match uu___8 with
                                                         | FStar_Pervasives_Native.Some
                                                             (kd, l, r) ->
                                                             let uu___9 =
                                                               FStar_InteractiveHelpers_Base.print_dbg
                                                                 dbg
                                                                 "The assertion is an equality" in
                                                             Obj.magic
                                                               (FStar_Tactics_Effect.tac_bind
                                                                  (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (625))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (625))
                                                                    (Prims.of_int (50)))))
                                                                  (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (626))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (645))
                                                                    (Prims.of_int (11)))))
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
                                                                    find_focused_in_term
                                                                    l in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (626))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (626))
                                                                    (Prims.of_int (40)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (626))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (645))
                                                                    (Prims.of_int (11)))))
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
                                                                    FStar_Pervasives_Native.Some
                                                                    res ->
                                                                    let uu___13
                                                                    =
                                                                    let uu___14
                                                                    =
                                                                    let uu___15
                                                                    =
                                                                    let uu___16
                                                                    =
                                                                    let uu___17
                                                                    =
                                                                    FStarC_Tactics_V1_Builtins.term_to_string
                                                                    l in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (629))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (629))
                                                                    (Prims.of_int (57)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (629))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (631))
                                                                    (Prims.of_int (63)))))
                                                                    (Obj.magic
                                                                    uu___17)
                                                                    (fun
                                                                    uu___18
                                                                    ->
                                                                    (fun
                                                                    uu___18
                                                                    ->
                                                                    let uu___19
                                                                    =
                                                                    let uu___20
                                                                    =
                                                                    let uu___21
                                                                    =
                                                                    FStarC_Tactics_V1_Builtins.term_to_string
                                                                    r in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (630))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (630))
                                                                    (Prims.of_int (57)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (630))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (631))
                                                                    (Prims.of_int (63)))))
                                                                    (Obj.magic
                                                                    uu___21)
                                                                    (fun
                                                                    uu___22
                                                                    ->
                                                                    (fun
                                                                    uu___22
                                                                    ->
                                                                    let uu___23
                                                                    =
                                                                    let uu___24
                                                                    =
                                                                    FStarC_Tactics_V1_Builtins.term_to_string
                                                                    res.res in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (631))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (631))
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
                                                                    uu___24)
                                                                    (fun
                                                                    uu___25
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___26
                                                                    ->
                                                                    Prims.strcat
                                                                    "\n- focused: "
                                                                    uu___25)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (631))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (631))
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
                                                                    uu___23)
                                                                    (fun
                                                                    uu___24
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___25
                                                                    ->
                                                                    Prims.strcat
                                                                    uu___22
                                                                    uu___24))))
                                                                    uu___22) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (630))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (631))
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
                                                                    uu___20)
                                                                    (fun
                                                                    uu___21
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___22
                                                                    ->
                                                                    Prims.strcat
                                                                    "\n- right  : "
                                                                    uu___21)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (630))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (631))
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
                                                                    uu___19)
                                                                    (fun
                                                                    uu___20
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___21
                                                                    ->
                                                                    Prims.strcat
                                                                    uu___18
                                                                    uu___20))))
                                                                    uu___18) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (629))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (631))
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
                                                                    uu___16)
                                                                    (fun
                                                                    uu___17
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___18
                                                                    ->
                                                                    Prims.strcat
                                                                    "\n- left   : "
                                                                    uu___17)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (629))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (631))
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
                                                                    "Found focused term in left operand:"
                                                                    uu___16)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (628))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (631))
                                                                    (Prims.of_int (64)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (628))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (631))
                                                                    (Prims.of_int (64)))))
                                                                    (Obj.magic
                                                                    uu___14)
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    uu___15))
                                                                    uu___15) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (628))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (631))
                                                                    (Prims.of_int (64)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (633))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (633))
                                                                    (Prims.of_int (29)))))
                                                                    (Obj.magic
                                                                    uu___13)
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    (l, res,
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    (fun t ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    mk_eq kd
                                                                    t r)))
                                                                    uu___16),
                                                                    true))))
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    let uu___13
                                                                    =
                                                                    find_focused_in_term
                                                                    r in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (635))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (635))
                                                                    (Prims.of_int (42)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (635))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (644))
                                                                    (Prims.of_int (89)))))
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
                                                                    FStar_Pervasives_Native.Some
                                                                    res ->
                                                                    let uu___15
                                                                    =
                                                                    let uu___16
                                                                    =
                                                                    let uu___17
                                                                    =
                                                                    let uu___18
                                                                    =
                                                                    let uu___19
                                                                    =
                                                                    FStarC_Tactics_V1_Builtins.term_to_string
                                                                    l in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (638))
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (638))
                                                                    (Prims.of_int (51)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (638))
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (640))
                                                                    (Prims.of_int (57)))))
                                                                    (Obj.magic
                                                                    uu___19)
                                                                    (fun
                                                                    uu___20
                                                                    ->
                                                                    (fun
                                                                    uu___20
                                                                    ->
                                                                    let uu___21
                                                                    =
                                                                    let uu___22
                                                                    =
                                                                    let uu___23
                                                                    =
                                                                    FStarC_Tactics_V1_Builtins.term_to_string
                                                                    r in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (639))
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (639))
                                                                    (Prims.of_int (51)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (639))
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (640))
                                                                    (Prims.of_int (57)))))
                                                                    (Obj.magic
                                                                    uu___23)
                                                                    (fun
                                                                    uu___24
                                                                    ->
                                                                    (fun
                                                                    uu___24
                                                                    ->
                                                                    let uu___25
                                                                    =
                                                                    let uu___26
                                                                    =
                                                                    FStarC_Tactics_V1_Builtins.term_to_string
                                                                    res.res in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (640))
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (640))
                                                                    (Prims.of_int (57)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___26)
                                                                    (fun
                                                                    uu___27
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___28
                                                                    ->
                                                                    Prims.strcat
                                                                    "\n- focused: "
                                                                    uu___27)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (640))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (640))
                                                                    (Prims.of_int (57)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___25)
                                                                    (fun
                                                                    uu___26
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___27
                                                                    ->
                                                                    Prims.strcat
                                                                    uu___24
                                                                    uu___26))))
                                                                    uu___24) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (639))
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (640))
                                                                    (Prims.of_int (57)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___22)
                                                                    (fun
                                                                    uu___23
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___24
                                                                    ->
                                                                    Prims.strcat
                                                                    "\n- right  : "
                                                                    uu___23)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (639))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (640))
                                                                    (Prims.of_int (57)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___21)
                                                                    (fun
                                                                    uu___22
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___23
                                                                    ->
                                                                    Prims.strcat
                                                                    uu___20
                                                                    uu___22))))
                                                                    uu___20) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (638))
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (640))
                                                                    (Prims.of_int (57)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___18)
                                                                    (fun
                                                                    uu___19
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___20
                                                                    ->
                                                                    Prims.strcat
                                                                    "\n- left   : "
                                                                    uu___19)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (638))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (640))
                                                                    (Prims.of_int (57)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___17)
                                                                    (fun
                                                                    uu___18
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___19
                                                                    ->
                                                                    Prims.strcat
                                                                    "Found focused term in right operand:"
                                                                    uu___18)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (637))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (640))
                                                                    (Prims.of_int (58)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (637))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (640))
                                                                    (Prims.of_int (58)))))
                                                                    (Obj.magic
                                                                    uu___16)
                                                                    (fun
                                                                    uu___17
                                                                    ->
                                                                    (fun
                                                                    uu___17
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    uu___17))
                                                                    uu___17) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (637))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (640))
                                                                    (Prims.of_int (58)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (642))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (642))
                                                                    (Prims.of_int (32)))))
                                                                    (Obj.magic
                                                                    uu___15)
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___17
                                                                    ->
                                                                    (r, res,
                                                                    (fun
                                                                    uu___18
                                                                    ->
                                                                    (fun t ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___18
                                                                    ->
                                                                    mk_eq kd
                                                                    l t)))
                                                                    uu___18),
                                                                    false))))
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.mfail
                                                                    "unfold_in_assert_or_assume: could not find a focused term in the assert"))
                                                                    uu___14)))
                                                                    uu___12)))
                                                                    uu___10))
                                                         | FStar_Pervasives_Native.None
                                                             ->
                                                             let uu___9 =
                                                               FStar_InteractiveHelpers_Base.print_dbg
                                                                 dbg
                                                                 "The assertion is not an equality" in
                                                             Obj.magic
                                                               (FStar_Tactics_Effect.tac_bind
                                                                  (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (648))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (648))
                                                                    (Prims.of_int (54)))))
                                                                  (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (649))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (649))
                                                                    (Prims.of_int (27)))))
                                                                  (Obj.magic
                                                                    uu___9)
                                                                  (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    Obj.magic
                                                                    (find_in_whole_term
                                                                    ()))
                                                                    uu___10)))
                                                        uu___8))) uu___6) in
                                    Obj.magic
                                      (FStar_Tactics_Effect.tac_bind
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "FStar.InteractiveHelpers.PostProcess.fst"
                                                  (Prims.of_int (621))
                                                  (Prims.of_int (69))
                                                  (Prims.of_int (649))
                                                  (Prims.of_int (27)))))
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "FStar.InteractiveHelpers.PostProcess.fst"
                                                  (Prims.of_int (612))
                                                  (Prims.of_int (4))
                                                  (Prims.of_int (735))
                                                  (Prims.of_int (30)))))
                                         (Obj.magic uu___4)
                                         (fun uu___5 ->
                                            (fun uu___5 ->
                                               match uu___5 with
                                               | (subterm, unf_res, rebuild,
                                                  insert_before) ->
                                                   let uu___6 =
                                                     Obj.magic
                                                       (FStar_Tactics_Effect.lift_div_tac
                                                          (fun uu___7 ->
                                                             rebuild)) in
                                                   Obj.magic
                                                     (FStar_Tactics_Effect.tac_bind
                                                        (FStar_Sealed.seal
                                                           (Obj.magic
                                                              (FStar_Range.mk_range
                                                                 "FStar.InteractiveHelpers.PostProcess.fst"
                                                                 (Prims.of_int (651))
                                                                 (Prims.of_int (2))
                                                                 (Prims.of_int (735))
                                                                 (Prims.of_int (30)))))
                                                        (FStar_Sealed.seal
                                                           (Obj.magic
                                                              (FStar_Range.mk_range
                                                                 "FStar.InteractiveHelpers.PostProcess.fst"
                                                                 (Prims.of_int (651))
                                                                 (Prims.of_int (2))
                                                                 (Prims.of_int (735))
                                                                 (Prims.of_int (30)))))
                                                        (Obj.magic uu___6)
                                                        (fun uu___7 ->
                                                           (fun rebuild1 ->
                                                              let uu___7 =
                                                                let uu___8 =
                                                                  let uu___9
                                                                    =
                                                                    let uu___10
                                                                    =
                                                                    let uu___11
                                                                    =
                                                                    FStarC_Tactics_V1_Builtins.term_to_string
                                                                    subterm in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (652))
                                                                    (Prims.of_int (33))
                                                                    (Prims.of_int (652))
                                                                    (Prims.of_int (55)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (652))
                                                                    (Prims.of_int (33))
                                                                    (Prims.of_int (653))
                                                                    (Prims.of_int (64)))))
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
                                                                    let uu___15
                                                                    =
                                                                    FStarC_Tactics_V1_Builtins.term_to_string
                                                                    unf_res.res in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (653))
                                                                    (Prims.of_int (38))
                                                                    (Prims.of_int (653))
                                                                    (Prims.of_int (64)))))
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
                                                                    "- focused term: "
                                                                    uu___16)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (653))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (653))
                                                                    (Prims.of_int (64)))))
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
                                                                    "\n"
                                                                    uu___15)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (652))
                                                                    (Prims.of_int (58))
                                                                    (Prims.of_int (653))
                                                                    (Prims.of_int (64)))))
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
                                                                    uu___12
                                                                    uu___14))))
                                                                    uu___12) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (652))
                                                                    (Prims.of_int (33))
                                                                    (Prims.of_int (653))
                                                                    (Prims.of_int (64)))))
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
                                                                    "- subterm: "
                                                                    uu___11)) in
                                                                  FStar_Tactics_Effect.tac_bind
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (652))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (653))
                                                                    (Prims.of_int (64)))))
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
                                                                    uu___9)
                                                                    (
                                                                    fun
                                                                    uu___10
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    Prims.strcat
                                                                    "Found subterm in assertion/assumption:\n"
                                                                    uu___10)) in
                                                                FStar_Tactics_Effect.tac_bind
                                                                  (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (651))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (653))
                                                                    (Prims.of_int (65)))))
                                                                  (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (651))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (653))
                                                                    (Prims.of_int (65)))))
                                                                  (Obj.magic
                                                                    uu___8)
                                                                  (fun uu___9
                                                                    ->
                                                                    (fun
                                                                    uu___9 ->
                                                                    Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    uu___9))
                                                                    uu___9) in
                                                              Obj.magic
                                                                (FStar_Tactics_Effect.tac_bind
                                                                   (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (651))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (653))
                                                                    (Prims.of_int (65)))))
                                                                   (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (653))
                                                                    (Prims.of_int (66))
                                                                    (Prims.of_int (735))
                                                                    (Prims.of_int (30)))))
                                                                   (Obj.magic
                                                                    uu___7)
                                                                   (fun
                                                                    uu___8 ->
                                                                    (fun
                                                                    uu___8 ->
                                                                    let uu___9
                                                                    =
                                                                    FStarC_Tactics_V1_Builtins.inspect
                                                                    unf_res.res in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (655))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (655))
                                                                    (Prims.of_int (36)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (655))
                                                                    (Prims.of_int (39))
                                                                    (Prims.of_int (735))
                                                                    (Prims.of_int (30)))))
                                                                    (Obj.magic
                                                                    uu___9)
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun
                                                                    res_view
                                                                    ->
                                                                    let uu___10
                                                                    =
                                                                    match res_view
                                                                    with
                                                                    | 
                                                                    FStarC_Reflection_V1_Data.Tv_FVar
                                                                    fv ->
                                                                    let uu___11
                                                                    =
                                                                    FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    (Prims.strcat
                                                                    "The focused term is a top identifier: "
                                                                    (FStar_Reflection_V1_Derived.fv_to_string
                                                                    fv)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (659))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (659))
                                                                    (Prims.of_int (80)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (659))
                                                                    (Prims.of_int (81))
                                                                    (Prims.of_int (664))
                                                                    (Prims.of_int (28)))))
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
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    FStar_Reflection_V1_Derived.flatten_name
                                                                    (FStarC_Reflection_V1_Builtins.inspect_fv
                                                                    fv))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (661))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (661))
                                                                    (Prims.of_int (46)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (661))
                                                                    (Prims.of_int (49))
                                                                    (Prims.of_int (664))
                                                                    (Prims.of_int (28)))))
                                                                    (Obj.magic
                                                                    uu___13)
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    (fun
                                                                    fname ->
                                                                    let uu___14
                                                                    =
                                                                    FStarC_Tactics_V1_Builtins.norm_term_env
                                                                    (ares.ge).FStar_InteractiveHelpers_Base.env
                                                                    [
                                                                    FStar_Pervasives.delta_only
                                                                    [fname];
                                                                    FStar_Pervasives.zeta]
                                                                    subterm in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (662))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (662))
                                                                    (Prims.of_int (81)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (663))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (664))
                                                                    (Prims.of_int (28)))))
                                                                    (Obj.magic
                                                                    uu___14)
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    (fun
                                                                    subterm'
                                                                    ->
                                                                    let uu___15
                                                                    =
                                                                    let uu___16
                                                                    =
                                                                    let uu___17
                                                                    =
                                                                    FStarC_Tactics_V1_Builtins.term_to_string
                                                                    subterm' in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (663))
                                                                    (Prims.of_int (46))
                                                                    (Prims.of_int (663))
                                                                    (Prims.of_int (69)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___17)
                                                                    (fun
                                                                    uu___18
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___19
                                                                    ->
                                                                    Prims.strcat
                                                                    "Normalized subterm: "
                                                                    uu___18)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (663))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (663))
                                                                    (Prims.of_int (70)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (663))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (663))
                                                                    (Prims.of_int (70)))))
                                                                    (Obj.magic
                                                                    uu___16)
                                                                    (fun
                                                                    uu___17
                                                                    ->
                                                                    (fun
                                                                    uu___17
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    uu___17))
                                                                    uu___17) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (663))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (663))
                                                                    (Prims.of_int (70)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (664))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (664))
                                                                    (Prims.of_int (28)))))
                                                                    (Obj.magic
                                                                    uu___15)
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___17
                                                                    ->
                                                                    ((ares.ge),
                                                                    (FStar_Pervasives_Native.Some
                                                                    subterm'))))))
                                                                    uu___15)))
                                                                    uu___14)))
                                                                    uu___12)
                                                                    | 
                                                                    uu___11
                                                                    ->
                                                                    let uu___12
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    FStar_List_Tot_Base.map
                                                                    FStar_Pervasives_Native.snd
                                                                    ares.parents)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (669))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (669))
                                                                    (Prims.of_int (49)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (669))
                                                                    (Prims.of_int (52))
                                                                    (Prims.of_int (696))
                                                                    (Prims.of_int (19)))))
                                                                    (Obj.magic
                                                                    uu___12)
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    (fun
                                                                    parents
                                                                    ->
                                                                    let uu___13
                                                                    =
                                                                    match res_view
                                                                    with
                                                                    | 
                                                                    FStarC_Reflection_V1_Data.Tv_Var
                                                                    bv ->
                                                                    let uu___14
                                                                    =
                                                                    let uu___15
                                                                    =
                                                                    let uu___16
                                                                    =
                                                                    FStar_Tactics_V1_Derived.bv_to_string
                                                                    bv in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (673))
                                                                    (Prims.of_int (68))
                                                                    (Prims.of_int (673))
                                                                    (Prims.of_int (83)))))
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
                                                                    "The focused term is a local variable: "
                                                                    uu___17)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (673))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (673))
                                                                    (Prims.of_int (84)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (673))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (673))
                                                                    (Prims.of_int (84)))))
                                                                    (Obj.magic
                                                                    uu___15)
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    uu___16))
                                                                    uu___16) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (673))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (673))
                                                                    (Prims.of_int (84)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (675))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (677))
                                                                    (Prims.of_int (39)))))
                                                                    (Obj.magic
                                                                    uu___14)
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    let uu___16
                                                                    =
                                                                    if
                                                                    Prims.op_Negation
                                                                    (FStar_Pervasives_Native.uu___is_Some
                                                                    (FStar_InteractiveHelpers_Base.genv_get
                                                                    ares.ge
                                                                    bv))
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_InteractiveHelpers_Base.mfail
                                                                    "unfold_in_assert_or_assume: can't unfold a variable locally introduced in an assertion"))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___18
                                                                    -> ()))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (675))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (676))
                                                                    (Prims.of_int (106)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (677))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (677))
                                                                    (Prims.of_int (39)))))
                                                                    (Obj.magic
                                                                    uu___16)
                                                                    (fun
                                                                    uu___17
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___18
                                                                    ->
                                                                    FStar_Pervasives_Native.Some
                                                                    (bv,
                                                                    (FStarC_Reflection_V2_Builtins.pack_ln
                                                                    FStarC_Reflection_V2_Data.Tv_Unknown))))))
                                                                    uu___15)
                                                                    | 
                                                                    uu___14
                                                                    ->
                                                                    let uu___15
                                                                    =
                                                                    let uu___16
                                                                    =
                                                                    let uu___17
                                                                    =
                                                                    FStarC_Tactics_V1_Builtins.term_to_string
                                                                    unf_res.res in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (679))
                                                                    (Prims.of_int (69))
                                                                    (Prims.of_int (679))
                                                                    (Prims.of_int (95)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___17)
                                                                    (fun
                                                                    uu___18
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___19
                                                                    ->
                                                                    Prims.strcat
                                                                    "The focused term is an arbitrary term: "
                                                                    uu___18)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (679))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (679))
                                                                    (Prims.of_int (96)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (679))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (679))
                                                                    (Prims.of_int (96)))))
                                                                    (Obj.magic
                                                                    uu___16)
                                                                    (fun
                                                                    uu___17
                                                                    ->
                                                                    (fun
                                                                    uu___17
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    uu___17))
                                                                    uu___17) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (679))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (679))
                                                                    (Prims.of_int (96)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (680))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (680))
                                                                    (Prims.of_int (14)))))
                                                                    (Obj.magic
                                                                    uu___15)
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___17
                                                                    ->
                                                                    FStar_Pervasives_Native.None)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (671))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (680))
                                                                    (Prims.of_int (14)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (681))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (696))
                                                                    (Prims.of_int (19)))))
                                                                    (Obj.magic
                                                                    uu___13)
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    (fun
                                                                    opt_bvty
                                                                    ->
                                                                    let uu___14
                                                                    =
                                                                    find_context_equality
                                                                    dbg
                                                                    ares.ge
                                                                    unf_res.res
                                                                    parents
                                                                    [] in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (682))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (682))
                                                                    (Prims.of_int (79)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (681))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (696))
                                                                    (Prims.of_int (19)))))
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
                                                                    (ge1,
                                                                    eq_tm) ->
                                                                    let uu___16
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___17
                                                                    ->
                                                                    match eq_tm
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    eq_tm1 ->
                                                                    FStar_Pervasives_Native.Some
                                                                    eq_tm1
                                                                    | 
                                                                    uu___18
                                                                    ->
                                                                    FStar_Pervasives_Native.None)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (685))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (687))
                                                                    (Prims.of_int (19)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (688))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (696))
                                                                    (Prims.of_int (19)))))
                                                                    (Obj.magic
                                                                    uu___16)
                                                                    (fun
                                                                    uu___17
                                                                    ->
                                                                    (fun
                                                                    opt_eq_tm
                                                                    ->
                                                                    let uu___17
                                                                    =
                                                                    match 
                                                                    (opt_bvty,
                                                                    opt_eq_tm)
                                                                    with
                                                                    | 
                                                                    (FStar_Pervasives_Native.Some
                                                                    bvty,
                                                                    FStar_Pervasives_Native.Some
                                                                    eq_tm1)
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (let uu___18
                                                                    =
                                                                    FStar_InteractiveHelpers_Base.apply_subst
                                                                    ge1.FStar_InteractiveHelpers_Base.env
                                                                    subterm
                                                                    [
                                                                    (bvty,
                                                                    eq_tm1)] in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (692))
                                                                    (Prims.of_int (40))
                                                                    (Prims.of_int (692))
                                                                    (Prims.of_int (85)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (692))
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (692))
                                                                    (Prims.of_int (85)))))
                                                                    (Obj.magic
                                                                    uu___18)
                                                                    (fun
                                                                    uu___19
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___20
                                                                    ->
                                                                    FStar_Pervasives_Native.Some
                                                                    uu___19))))
                                                                    | 
                                                                    (FStar_Pervasives_Native.None,
                                                                    FStar_Pervasives_Native.Some
                                                                    eq_tm1)
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (let uu___18
                                                                    =
                                                                    replace_term_in
                                                                    dbg
                                                                    unf_res.res
                                                                    eq_tm1
                                                                    subterm in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (693))
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (693))
                                                                    (Prims.of_int (82)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (693))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (693))
                                                                    (Prims.of_int (82)))))
                                                                    (Obj.magic
                                                                    uu___18)
                                                                    (fun
                                                                    uu___19
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___20
                                                                    ->
                                                                    FStar_Pervasives_Native.Some
                                                                    uu___19))))
                                                                    | 
                                                                    uu___18
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___19
                                                                    ->
                                                                    FStar_Pervasives_Native.None))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (691))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (694))
                                                                    (Prims.of_int (19)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (696))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (696))
                                                                    (Prims.of_int (19)))))
                                                                    (Obj.magic
                                                                    uu___17)
                                                                    (fun
                                                                    subterm'
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___18
                                                                    ->
                                                                    (ge1,
                                                                    subterm')))))
                                                                    uu___17)))
                                                                    uu___15)))
                                                                    uu___14)))
                                                                    uu___13) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (657))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (696))
                                                                    (Prims.of_int (19)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (655))
                                                                    (Prims.of_int (39))
                                                                    (Prims.of_int (735))
                                                                    (Prims.of_int (30)))))
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
                                                                    (ge1,
                                                                    opt_unf_tm)
                                                                    ->
                                                                    let uu___12
                                                                    =
                                                                    match opt_unf_tm
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    unf_tm ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    (ge1,
                                                                    unf_tm))))
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (let uu___13
                                                                    =
                                                                    let uu___14
                                                                    =
                                                                    strip_implicit_parameters
                                                                    unf_res.res in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (710))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (710))
                                                                    (Prims.of_int (65)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (710))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (710))
                                                                    (Prims.of_int (65)))))
                                                                    (Obj.magic
                                                                    uu___14)
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    Obj.magic
                                                                    (FStarC_Tactics_V1_Builtins.inspect
                                                                    uu___15))
                                                                    uu___15) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (710))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (710))
                                                                    (Prims.of_int (65)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (710))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (722))
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
                                                                    FStarC_Reflection_V1_Data.Tv_FVar
                                                                    fv ->
                                                                    let uu___15
                                                                    =
                                                                    FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    (Prims.strcat
                                                                    "The focused term is a top identifier with implicit parameters: "
                                                                    (FStar_Reflection_V1_Derived.fv_to_string
                                                                    fv)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (712))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (713))
                                                                    (Prims.of_int (41)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (713))
                                                                    (Prims.of_int (42))
                                                                    (Prims.of_int (718))
                                                                    (Prims.of_int (21)))))
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
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___18
                                                                    ->
                                                                    FStar_Reflection_V1_Derived.flatten_name
                                                                    (FStarC_Reflection_V1_Builtins.inspect_fv
                                                                    fv))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (715))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (715))
                                                                    (Prims.of_int (48)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (715))
                                                                    (Prims.of_int (51))
                                                                    (Prims.of_int (718))
                                                                    (Prims.of_int (21)))))
                                                                    (Obj.magic
                                                                    uu___17)
                                                                    (fun
                                                                    uu___18
                                                                    ->
                                                                    (fun
                                                                    fname ->
                                                                    let uu___18
                                                                    =
                                                                    FStarC_Tactics_V1_Builtins.norm_term_env
                                                                    ge1.FStar_InteractiveHelpers_Base.env
                                                                    [
                                                                    FStar_Pervasives.delta_only
                                                                    [fname];
                                                                    FStar_Pervasives.zeta]
                                                                    subterm in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (716))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (716))
                                                                    (Prims.of_int (79)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (717))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (718))
                                                                    (Prims.of_int (21)))))
                                                                    (Obj.magic
                                                                    uu___18)
                                                                    (fun
                                                                    uu___19
                                                                    ->
                                                                    (fun
                                                                    subterm'
                                                                    ->
                                                                    let uu___19
                                                                    =
                                                                    let uu___20
                                                                    =
                                                                    let uu___21
                                                                    =
                                                                    FStarC_Tactics_V1_Builtins.term_to_string
                                                                    subterm' in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (717))
                                                                    (Prims.of_int (48))
                                                                    (Prims.of_int (717))
                                                                    (Prims.of_int (71)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___21)
                                                                    (fun
                                                                    uu___22
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___23
                                                                    ->
                                                                    Prims.strcat
                                                                    "Normalized subterm: "
                                                                    uu___22)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (717))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (717))
                                                                    (Prims.of_int (72)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (717))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (717))
                                                                    (Prims.of_int (72)))))
                                                                    (Obj.magic
                                                                    uu___20)
                                                                    (fun
                                                                    uu___21
                                                                    ->
                                                                    (fun
                                                                    uu___21
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    uu___21))
                                                                    uu___21) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (717))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (717))
                                                                    (Prims.of_int (72)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (718))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (718))
                                                                    (Prims.of_int (21)))))
                                                                    (Obj.magic
                                                                    uu___19)
                                                                    (fun
                                                                    uu___20
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___21
                                                                    ->
                                                                    (ge1,
                                                                    subterm')))))
                                                                    uu___19)))
                                                                    uu___18)))
                                                                    uu___16))
                                                                    | 
                                                                    uu___15
                                                                    ->
                                                                    let uu___16
                                                                    =
                                                                    let uu___17
                                                                    =
                                                                    let uu___18
                                                                    =
                                                                    FStarC_Tactics_V1_Builtins.term_to_string
                                                                    unf_res.res in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (722))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (722))
                                                                    (Prims.of_int (41)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___18)
                                                                    (fun
                                                                    uu___19
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___20
                                                                    ->
                                                                    Prims.strcat
                                                                    "couldn't find equalities with which to rewrite: "
                                                                    uu___19)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (721))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (722))
                                                                    (Prims.of_int (41)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___17)
                                                                    (fun
                                                                    uu___18
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___19
                                                                    ->
                                                                    Prims.strcat
                                                                    "unfold_in_assert_or_assume: "
                                                                    uu___18)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (720))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (722))
                                                                    (Prims.of_int (42)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (720))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (722))
                                                                    (Prims.of_int (42)))))
                                                                    (Obj.magic
                                                                    uu___16)
                                                                    (fun
                                                                    uu___17
                                                                    ->
                                                                    (fun
                                                                    uu___17
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.mfail
                                                                    uu___17))
                                                                    uu___17)))
                                                                    uu___14))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (707))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (723))
                                                                    (Prims.of_int (9)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (697))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (735))
                                                                    (Prims.of_int (30)))))
                                                                    (Obj.magic
                                                                    uu___12)
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    match uu___13
                                                                    with
                                                                    | 
                                                                    (ge2,
                                                                    unf_tm)
                                                                    ->
                                                                    let uu___14
                                                                    =
                                                                    rebuild1
                                                                    unf_tm in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (726))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (726))
                                                                    (Prims.of_int (35)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (726))
                                                                    (Prims.of_int (38))
                                                                    (Prims.of_int (735))
                                                                    (Prims.of_int (30)))))
                                                                    (Obj.magic
                                                                    uu___14)
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    (fun
                                                                    final_assert
                                                                    ->
                                                                    let uu___15
                                                                    =
                                                                    FStar_InteractiveHelpers_Base.prettify_term
                                                                    dbg
                                                                    final_assert in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (727))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (727))
                                                                    (Prims.of_int (51)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (728))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (735))
                                                                    (Prims.of_int (30)))))
                                                                    (Obj.magic
                                                                    uu___15)
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    (fun
                                                                    final_assert1
                                                                    ->
                                                                    let uu___16
                                                                    =
                                                                    let uu___17
                                                                    =
                                                                    let uu___18
                                                                    =
                                                                    FStarC_Tactics_V1_Builtins.term_to_string
                                                                    final_assert1 in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (728))
                                                                    (Prims.of_int (43))
                                                                    (Prims.of_int (728))
                                                                    (Prims.of_int (70)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___18)
                                                                    (fun
                                                                    uu___19
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___20
                                                                    ->
                                                                    Prims.strcat
                                                                    "-> Final assertion:\n"
                                                                    uu___19)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (728))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (728))
                                                                    (Prims.of_int (71)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (728))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (728))
                                                                    (Prims.of_int (71)))))
                                                                    (Obj.magic
                                                                    uu___17)
                                                                    (fun
                                                                    uu___18
                                                                    ->
                                                                    (fun
                                                                    uu___18
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    uu___18))
                                                                    uu___18) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (728))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (728))
                                                                    (Prims.of_int (71)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (728))
                                                                    (Prims.of_int (72))
                                                                    (Prims.of_int (735))
                                                                    (Prims.of_int (30)))))
                                                                    (Obj.magic
                                                                    uu___16)
                                                                    (fun
                                                                    uu___17
                                                                    ->
                                                                    (fun
                                                                    uu___17
                                                                    ->
                                                                    let uu___18
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___19
                                                                    ->
                                                                    if
                                                                    insert_before
                                                                    then
                                                                    FStar_InteractiveHelpers_Propositions.mk_assertions
                                                                    [final_assert1]
                                                                    []
                                                                    else
                                                                    FStar_InteractiveHelpers_Propositions.mk_assertions
                                                                    []
                                                                    [final_assert1])) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (730))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (730))
                                                                    (Prims.of_int (94)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (731))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (735))
                                                                    (Prims.of_int (30)))))
                                                                    (Obj.magic
                                                                    uu___18)
                                                                    (fun
                                                                    uu___19
                                                                    ->
                                                                    (fun
                                                                    asserts
                                                                    ->
                                                                    let uu___19
                                                                    =
                                                                    FStar_InteractiveHelpers_Output.subst_shadowed_with_abs_in_assertions
                                                                    dbg ge2
                                                                    FStar_Pervasives_Native.None
                                                                    asserts in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (733))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (733))
                                                                    (Prims.of_int (79)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (731))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (735))
                                                                    (Prims.of_int (30)))))
                                                                    (Obj.magic
                                                                    uu___19)
                                                                    (fun
                                                                    uu___20
                                                                    ->
                                                                    (fun
                                                                    uu___20
                                                                    ->
                                                                    match uu___20
                                                                    with
                                                                    | 
                                                                    (ge3,
                                                                    asserts1)
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_InteractiveHelpers_Output.printout_success
                                                                    ge3
                                                                    asserts1))
                                                                    uu___20)))
                                                                    uu___19)))
                                                                    uu___17)))
                                                                    uu___16)))
                                                                    uu___15)))
                                                                    uu___13)))
                                                                    uu___11)))
                                                                    uu___10)))
                                                                    uu___8)))
                                                             uu___7))) uu___5)))
                                   uu___4))) uu___3))) uu___1)
let (pp_unfold_in_assert_or_assume :
  Prims.bool -> unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun dbg ->
    fun uu___ ->
      FStar_Tactics_V1_Derived.try_with
        (fun uu___1 ->
           match () with
           | () ->
               let uu___2 = find_focused_assert_in_current_goal dbg in
               FStar_Tactics_Effect.tac_bind
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range
                          "FStar.InteractiveHelpers.PostProcess.fst"
                          (Prims.of_int (741)) (Prims.of_int (14))
                          (Prims.of_int (741)) (Prims.of_int (53)))))
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range
                          "FStar.InteractiveHelpers.PostProcess.fst"
                          (Prims.of_int (742)) (Prims.of_int (4))
                          (Prims.of_int (743)) (Prims.of_int (16)))))
                 (Obj.magic uu___2)
                 (fun uu___3 ->
                    (fun res ->
                       let uu___3 = unfold_in_assert_or_assume dbg res in
                       Obj.magic
                         (FStar_Tactics_Effect.tac_bind
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.InteractiveHelpers.PostProcess.fst"
                                     (Prims.of_int (742)) (Prims.of_int (4))
                                     (Prims.of_int (742)) (Prims.of_int (38)))))
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.InteractiveHelpers.PostProcess.fst"
                                     (Prims.of_int (743)) (Prims.of_int (4))
                                     (Prims.of_int (743)) (Prims.of_int (16)))))
                            (Obj.magic uu___3)
                            (fun uu___4 ->
                               (fun uu___4 -> Obj.magic (end_proof ()))
                                 uu___4))) uu___3))
        (fun uu___1 ->
           (fun uu___1 ->
              match uu___1 with
              | FStar_InteractiveHelpers_Base.MetaAnalysis msg ->
                  Obj.magic
                    (Obj.repr
                       (let uu___2 =
                          FStar_InteractiveHelpers_Output.printout_failure
                            msg in
                        FStar_Tactics_Effect.tac_bind
                          (FStar_Sealed.seal
                             (Obj.magic
                                (FStar_Range.mk_range
                                   "FStar.InteractiveHelpers.PostProcess.fst"
                                   (Prims.of_int (744)) (Prims.of_int (29))
                                   (Prims.of_int (744)) (Prims.of_int (49)))))
                          (FStar_Sealed.seal
                             (Obj.magic
                                (FStar_Range.mk_range
                                   "FStar.InteractiveHelpers.PostProcess.fst"
                                   (Prims.of_int (744)) (Prims.of_int (51))
                                   (Prims.of_int (744)) (Prims.of_int (63)))))
                          (Obj.magic uu___2)
                          (fun uu___3 ->
                             (fun uu___3 -> Obj.magic (end_proof ())) uu___3)))
              | err -> Obj.magic (Obj.repr (FStar_Tactics_Effect.raise err)))
             uu___1)
let _ =
  FStarC_Tactics_Native.register_tactic
    "FStar.InteractiveHelpers.PostProcess.pp_unfold_in_assert_or_assume"
    (Prims.of_int (3))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             FStarC_Tactics_InterpFuns.mk_tactic_interpretation_2
               "FStar.InteractiveHelpers.PostProcess.pp_unfold_in_assert_or_assume (plugin)"
               (FStarC_Tactics_Native.from_tactic_2
                  pp_unfold_in_assert_or_assume)
               FStarC_Syntax_Embeddings.e_bool
               FStarC_Syntax_Embeddings.e_unit
               FStarC_Syntax_Embeddings.e_unit psc ncb us args)