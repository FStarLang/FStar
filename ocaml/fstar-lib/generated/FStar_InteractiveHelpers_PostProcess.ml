open Prims
let (term_eq :
  FStar_Reflection_Types.term ->
    FStar_Reflection_Types.term ->
      (Prims.bool, unit) FStar_Tactics_Effect.tac_repr)
  = FStar_Tactics_Builtins.term_eq_old
type meta_info = unit
let (focus_on_term : meta_info) =
  Obj.magic (fun uu___ -> failwith "Not yet implemented:focus_on_term")
let (end_proof : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    FStar_Tactics_Builtins.tadmit_t
      (FStar_Reflection_Builtins.pack_ln
         (FStar_Reflection_Data.Tv_Const FStar_Reflection_Data.C_Unit))
let (unsquash_equality :
  FStar_Reflection_Types.term ->
    ((FStar_Reflection_Types.term * FStar_Reflection_Types.term)
       FStar_Pervasives_Native.option,
      unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    FStar_Tactics_Effect.tac_bind
      (Prims.mk_range "FStar.InteractiveHelpers.PostProcess.fst"
         (Prims.of_int (33)) (Prims.of_int (14)) (Prims.of_int (33))
         (Prims.of_int (31)))
      (Prims.mk_range "FStar.InteractiveHelpers.PostProcess.fst"
         (Prims.of_int (33)) (Prims.of_int (8)) (Prims.of_int (35))
         (Prims.of_int (13)))
      (Obj.magic (FStar_Reflection_Formula.term_as_formula t))
      (fun uu___ ->
         FStar_Tactics_Effect.lift_div_tac
           (fun uu___1 ->
              match uu___ with
              | FStar_Reflection_Formula.Comp
                  (FStar_Reflection_Formula.Eq uu___2, l, r) ->
                  FStar_Pervasives_Native.Some (l, r)
              | uu___2 -> FStar_Pervasives_Native.None))
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
            FStar_Tactics_Effect.tac_bind
              (Prims.mk_range "FStar.InteractiveHelpers.PostProcess.fst"
                 (Prims.of_int (44)) (Prims.of_int (10)) (Prims.of_int (44))
                 (Prims.of_int (21)))
              (Prims.mk_range "FStar.InteractiveHelpers.PostProcess.fst"
                 (Prims.of_int (45)) (Prims.of_int (2)) (Prims.of_int (55))
                 (Prims.of_int (5)))
              (Obj.magic (FStar_Tactics_Derived.cur_goal ()))
              (fun uu___ ->
                 (fun g ->
                    Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (Prims.mk_range
                            "FStar.InteractiveHelpers.PostProcess.fst"
                            (Prims.of_int (45)) (Prims.of_int (10))
                            (Prims.of_int (45)) (Prims.of_int (20)))
                         (Prims.mk_range
                            "FStar.InteractiveHelpers.PostProcess.fst"
                            (Prims.of_int (46)) (Prims.of_int (2))
                            (Prims.of_int (55)) (Prims.of_int (5)))
                         (Obj.magic (FStar_Tactics_Derived.cur_env ()))
                         (fun uu___ ->
                            (fun e ->
                               Obj.magic
                                 (FStar_Tactics_Effect.tac_bind
                                    (Prims.mk_range
                                       "FStar.InteractiveHelpers.PostProcess.fst"
                                       (Prims.of_int (46)) (Prims.of_int (2))
                                       (Prims.of_int (46))
                                       (Prims.of_int (55)))
                                    (Prims.mk_range
                                       "FStar.InteractiveHelpers.PostProcess.fst"
                                       (Prims.of_int (47)) (Prims.of_int (8))
                                       (Prims.of_int (54))
                                       (Prims.of_int (52)))
                                    (Obj.magic
                                       (FStar_Tactics_Effect.tac_bind
                                          (Prims.mk_range
                                             "FStar.InteractiveHelpers.PostProcess.fst"
                                             (Prims.of_int (46))
                                             (Prims.of_int (16))
                                             (Prims.of_int (46))
                                             (Prims.of_int (55)))
                                          (Prims.mk_range
                                             "FStar.InteractiveHelpers.PostProcess.fst"
                                             (Prims.of_int (46))
                                             (Prims.of_int (2))
                                             (Prims.of_int (46))
                                             (Prims.of_int (55)))
                                          (Obj.magic
                                             (FStar_Tactics_Effect.tac_bind
                                                (Prims.mk_range
                                                   "FStar.InteractiveHelpers.PostProcess.fst"
                                                   (Prims.of_int (46))
                                                   (Prims.of_int (38))
                                                   (Prims.of_int (46))
                                                   (Prims.of_int (54)))
                                                (Prims.mk_range "prims.fst"
                                                   (Prims.of_int (606))
                                                   (Prims.of_int (19))
                                                   (Prims.of_int (606))
                                                   (Prims.of_int (31)))
                                                (Obj.magic
                                                   (FStar_Tactics_Builtins.term_to_string
                                                      g))
                                                (fun uu___ ->
                                                   FStar_Tactics_Effect.lift_div_tac
                                                     (fun uu___1 ->
                                                        Prims.strcat
                                                          "[> pp_explore:\n"
                                                          uu___))))
                                          (fun uu___ ->
                                             (fun uu___ ->
                                                Obj.magic
                                                  (FStar_InteractiveHelpers_Base.print_dbg
                                                     dbg uu___)) uu___)))
                                    (fun uu___ ->
                                       (fun uu___ ->
                                          Obj.magic
                                            (FStar_Tactics_Effect.tac_bind
                                               (Prims.mk_range
                                                  "FStar.InteractiveHelpers.PostProcess.fst"
                                                  (Prims.of_int (47))
                                                  (Prims.of_int (14))
                                                  (Prims.of_int (47))
                                                  (Prims.of_int (33)))
                                               (Prims.mk_range
                                                  "FStar.InteractiveHelpers.PostProcess.fst"
                                                  (Prims.of_int (47))
                                                  (Prims.of_int (8))
                                                  (Prims.of_int (54))
                                                  (Prims.of_int (52)))
                                               (Obj.magic
                                                  (unsquash_equality g))
                                               (fun uu___1 ->
                                                  (fun uu___1 ->
                                                     match uu___1 with
                                                     | FStar_Pervasives_Native.Some
                                                         (l, uu___2) ->
                                                         Obj.magic
                                                           (FStar_Tactics_Effect.tac_bind
                                                              (Prims.mk_range
                                                                 "FStar.InteractiveHelpers.PostProcess.fst"
                                                                 (Prims.of_int (49))
                                                                 (Prims.of_int (12))
                                                                 (Prims.of_int (49))
                                                                 (Prims.of_int (36)))
                                                              (Prims.mk_range
                                                                 "FStar.InteractiveHelpers.PostProcess.fst"
                                                                 (Prims.of_int (50))
                                                                 (Prims.of_int (4))
                                                                 (Prims.of_int (53))
                                                                 (Prims.of_int (16)))
                                                              (Obj.magic
                                                                 (FStar_InteractiveHelpers_ExploreTerm.safe_typ_or_comp
                                                                    dbg e l))
                                                              (fun uu___3 ->
                                                                 (fun c ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (28)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (51))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (53))
                                                                    (Prims.of_int (16)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_InteractiveHelpers_Base.mk_genv
                                                                    e [] []))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun ge
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (51))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (51))
                                                                    (Prims.of_int (68)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (52))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (53))
                                                                    (Prims.of_int (16)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (51))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (51))
                                                                    (Prims.of_int (68)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (51))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (51))
                                                                    (Prims.of_int (68)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (51))
                                                                    (Prims.of_int (51))
                                                                    (Prims.of_int (51))
                                                                    (Prims.of_int (67)))
                                                                    (Prims.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (606))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (606))
                                                                    (Prims.of_int (31)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Builtins.term_to_string
                                                                    l))
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    Prims.strcat
                                                                    "[> About to explore term:\n"
                                                                    uu___3))))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    uu___3))
                                                                    uu___3)))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (52))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (52))
                                                                    (Prims.of_int (49)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (53))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (53))
                                                                    (Prims.of_int (16)))
                                                                    (Obj.magic
                                                                    (FStar_InteractiveHelpers_ExploreTerm.explore_term
                                                                    dbg dfs
                                                                    () f x ge
                                                                    [] c l))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun x1
                                                                    ->
                                                                    Obj.magic
                                                                    (end_proof
                                                                    ()))
                                                                    uu___4)))
                                                                    uu___3)))
                                                                    uu___3)))
                                                                   uu___3))
                                                     | uu___2 ->
                                                         Obj.magic
                                                           (FStar_InteractiveHelpers_Base.mfail
                                                              "pp_explore: not a squashed equality"))
                                                    uu___1))) uu___))) uu___)))
                   uu___)
let (pp_explore_print_goal :
  unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    FStar_Tactics_Effect.tac_bind
      (Prims.mk_range "FStar.InteractiveHelpers.PostProcess.fst"
         (Prims.of_int (63)) (Prims.of_int (4)) (Prims.of_int (63))
         (Prims.of_int (35)))
      (Prims.mk_range "FStar.InteractiveHelpers.PostProcess.fst"
         (Prims.of_int (65)) (Prims.of_int (2)) (Prims.of_int (65))
         (Prims.of_int (28)))
      (FStar_Tactics_Effect.lift_div_tac
         (fun uu___1 ->
            (fun uu___1 ->
               Obj.magic
                 (fun uu___2 ->
                    fun uu___3 ->
                      fun uu___4 ->
                        fun uu___5 ->
                          fun uu___6 ->
                            FStar_Tactics_Effect.lift_div_tac
                              (fun uu___7 ->
                                 ((), FStar_Tactics_Types.Continue)))) uu___1))
      (fun uu___1 ->
         (fun f ->
            Obj.magic (pp_explore true false () (Obj.magic f) (Obj.repr ())))
           uu___1)
let (is_focus_on_term :
  FStar_Reflection_Types.term ->
    (Prims.bool, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___ ->
    (fun t ->
       Obj.magic
         (FStar_Tactics_Effect.lift_div_tac
            (fun uu___ ->
               FStar_Reflection_Derived.is_fvar t
                 "FStar.InteractiveHelpers.PostProcess.focus_on_term")))
      uu___
let (term_is_assert_or_assume :
  FStar_Reflection_Types.term ->
    (FStar_Reflection_Types.term FStar_Pervasives_Native.option, unit)
      FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    FStar_Tactics_Effect.tac_bind
      (Prims.mk_range "FStar.InteractiveHelpers.PostProcess.fst"
         (Prims.of_int (76)) (Prims.of_int (8)) (Prims.of_int (76))
         (Prims.of_int (17)))
      (Prims.mk_range "FStar.InteractiveHelpers.PostProcess.fst"
         (Prims.of_int (76)) (Prims.of_int (2)) (Prims.of_int (81))
         (Prims.of_int (13))) (Obj.magic (FStar_Tactics_Builtins.inspect t))
      (fun uu___ ->
         FStar_Tactics_Effect.lift_div_tac
           (fun uu___1 ->
              match uu___ with
              | FStar_Reflection_Data.Tv_App
                  (hd, (a, FStar_Reflection_Data.Q_Explicit)) ->
                  if
                    FStar_Reflection_Derived.is_any_fvar a
                      ["Prims._assert";
                      "FStar.Pervasives.assert_norm";
                      "Prims._assume"]
                  then FStar_Pervasives_Native.Some a
                  else FStar_Pervasives_Native.None
              | uu___2 -> FStar_Pervasives_Native.None))
let (is_focused_term :
  FStar_Reflection_Data.term_view ->
    (FStar_Reflection_Types.term FStar_Pervasives_Native.option, unit)
      FStar_Tactics_Effect.tac_repr)
  =
  fun uu___ ->
    (fun tv ->
       match tv with
       | FStar_Reflection_Data.Tv_Let (recf, attrs, uu___, def, body) ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.tac_bind
                   (Prims.mk_range "FStar.InteractiveHelpers.PostProcess.fst"
                      (Prims.of_int (89)) (Prims.of_int (7))
                      (Prims.of_int (89)) (Prims.of_int (27)))
                   (Prims.mk_range "FStar.InteractiveHelpers.PostProcess.fst"
                      (Prims.of_int (89)) (Prims.of_int (4))
                      (Prims.of_int (89)) (Prims.of_int (52)))
                   (Obj.magic (is_focus_on_term def))
                   (fun uu___1 ->
                      FStar_Tactics_Effect.lift_div_tac
                        (fun uu___2 ->
                           if uu___1
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
    (FStar_InteractiveHelpers_Base.genv * FStar_Reflection_Data.term_view)
      Prims.list
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
      (FStar_InteractiveHelpers_Base.genv * FStar_Reflection_Data.term_view)
        Prims.list
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
          FStar_Reflection_Data.term_view) Prims.list ->
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
    (FStar_InteractiveHelpers_Base.genv * FStar_Reflection_Data.term_view)
      Prims.list ->
      FStar_InteractiveHelpers_ExploreTerm.typ_or_comp
        FStar_Pervasives_Native.option ->
        FStar_Reflection_Data.term_view ->
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
                FStar_Tactics_Effect.tac_bind
                  (Prims.mk_range "FStar.InteractiveHelpers.PostProcess.fst"
                     (Prims.of_int (108)) (Prims.of_int (2))
                     (Prims.of_int (108)) (Prims.of_int (77)))
                  (Prims.mk_range "FStar.InteractiveHelpers.PostProcess.fst"
                     (Prims.of_int (109)) (Prims.of_int (2))
                     (Prims.of_int (115)) (Prims.of_int (26)))
                  (if FStar_Pervasives_Native.uu___is_Some acc
                   then
                     Obj.magic
                       (Obj.repr
                          (FStar_InteractiveHelpers_Base.mfail
                             "find_focused_term_explorer: non empty accumulator"))
                   else
                     Obj.magic
                       (Obj.repr
                          (FStar_Tactics_Effect.lift_div_tac
                             (fun uu___1 -> ()))))
                  (fun uu___ ->
                     (fun uu___ ->
                        Obj.magic
                          (FStar_Tactics_Effect.tac_bind
                             (Prims.mk_range
                                "FStar.InteractiveHelpers.PostProcess.fst"
                                (Prims.of_int (109)) (Prims.of_int (2))
                                (Prims.of_int (112)) (Prims.of_int (7)))
                             (Prims.mk_range
                                "FStar.InteractiveHelpers.PostProcess.fst"
                                (Prims.of_int (113)) (Prims.of_int (2))
                                (Prims.of_int (115)) (Prims.of_int (26)))
                             (if dbg
                              then
                                Obj.magic
                                  (Obj.repr
                                     (FStar_Tactics_Effect.tac_bind
                                        (Prims.mk_range
                                           "FStar.InteractiveHelpers.PostProcess.fst"
                                           (Prims.of_int (111))
                                           (Prims.of_int (10))
                                           (Prims.of_int (111))
                                           (Prims.of_int (96)))
                                        (Prims.mk_range
                                           "FStar.InteractiveHelpers.PostProcess.fst"
                                           (Prims.of_int (111))
                                           (Prims.of_int (4))
                                           (Prims.of_int (111))
                                           (Prims.of_int (96)))
                                        (Obj.magic
                                           (FStar_Tactics_Effect.tac_bind
                                              (Prims.mk_range
                                                 "FStar.InteractiveHelpers.PostProcess.fst"
                                                 (Prims.of_int (111))
                                                 (Prims.of_int (47))
                                                 (Prims.of_int (111))
                                                 (Prims.of_int (95)))
                                              (Prims.mk_range "prims.fst"
                                                 (Prims.of_int (606))
                                                 (Prims.of_int (19))
                                                 (Prims.of_int (606))
                                                 (Prims.of_int (31)))
                                              (Obj.magic
                                                 (FStar_Tactics_Effect.tac_bind
                                                    (Prims.mk_range
                                                       "FStar.InteractiveHelpers.PostProcess.fst"
                                                       (Prims.of_int (111))
                                                       (Prims.of_int (47))
                                                       (Prims.of_int (111))
                                                       (Prims.of_int (68)))
                                                    (Prims.mk_range
                                                       "FStar.InteractiveHelpers.PostProcess.fst"
                                                       (Prims.of_int (111))
                                                       (Prims.of_int (47))
                                                       (Prims.of_int (111))
                                                       (Prims.of_int (95)))
                                                    (Obj.magic
                                                       (FStar_InteractiveHelpers_Base.term_view_construct
                                                          t))
                                                    (fun uu___1 ->
                                                       (fun uu___1 ->
                                                          Obj.magic
                                                            (FStar_Tactics_Effect.tac_bind
                                                               (Prims.mk_range
                                                                  "FStar.InteractiveHelpers.PostProcess.fst"
                                                                  (Prims.of_int (111))
                                                                  (Prims.of_int (71))
                                                                  (Prims.of_int (111))
                                                                  (Prims.of_int (95)))
                                                               (Prims.mk_range
                                                                  "prims.fst"
                                                                  (Prims.of_int (606))
                                                                  (Prims.of_int (19))
                                                                  (Prims.of_int (606))
                                                                  (Prims.of_int (31)))
                                                               (Obj.magic
                                                                  (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (111))
                                                                    (Prims.of_int (79))
                                                                    (Prims.of_int (111))
                                                                    (Prims.of_int (95)))
                                                                    (Prims.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (606))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (606))
                                                                    (Prims.of_int (31)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (107))
                                                                    (Prims.of_int (62))
                                                                    (Prims.of_int (107))
                                                                    (Prims.of_int (63)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (111))
                                                                    (Prims.of_int (79))
                                                                    (Prims.of_int (111))
                                                                    (Prims.of_int (95)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Builtins.pack
                                                                    t))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    uu___2 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Builtins.term_to_string
                                                                    uu___2))
                                                                    uu___2)))
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    Prims.strcat
                                                                    ":\n"
                                                                    uu___2))))
                                                               (fun uu___2 ->
                                                                  FStar_Tactics_Effect.lift_div_tac
                                                                    (
                                                                    fun
                                                                    uu___3 ->
                                                                    Prims.strcat
                                                                    uu___1
                                                                    uu___2))))
                                                         uu___1)))
                                              (fun uu___1 ->
                                                 FStar_Tactics_Effect.lift_div_tac
                                                   (fun uu___2 ->
                                                      Prims.strcat
                                                        "[> find_focused_term_explorer: "
                                                        uu___1))))
                                        (fun uu___1 ->
                                           (fun uu___1 ->
                                              Obj.magic
                                                (FStar_Tactics_Builtins.print
                                                   uu___1)) uu___1)))
                              else
                                Obj.magic
                                  (Obj.repr
                                     (FStar_Tactics_Effect.lift_div_tac
                                        (fun uu___2 -> ()))))
                             (fun uu___1 ->
                                (fun uu___1 ->
                                   Obj.magic
                                     (FStar_Tactics_Effect.tac_bind
                                        (Prims.mk_range
                                           "FStar.InteractiveHelpers.PostProcess.fst"
                                           (Prims.of_int (113))
                                           (Prims.of_int (8))
                                           (Prims.of_int (113))
                                           (Prims.of_int (26)))
                                        (Prims.mk_range
                                           "FStar.InteractiveHelpers.PostProcess.fst"
                                           (Prims.of_int (113))
                                           (Prims.of_int (2))
                                           (Prims.of_int (115))
                                           (Prims.of_int (26)))
                                        (Obj.magic (pred ge pl opt_c t))
                                        (fun uu___2 ->
                                           FStar_Tactics_Effect.lift_div_tac
                                             (fun uu___3 ->
                                                match uu___2 with
                                                | FStar_Pervasives_Native.Some
                                                    ft ->
                                                    ((FStar_Pervasives_Native.Some
                                                        ((mk_exploration_result
                                                            ()) ge pl opt_c
                                                           ft)),
                                                      FStar_Tactics_Types.Abort)
                                                | FStar_Pervasives_Native.None
                                                    ->
                                                    (FStar_Pervasives_Native.None,
                                                      FStar_Tactics_Types.Continue)))))
                                  uu___1))) uu___)
let find_predicated_term :
  'a .
    'a pred_explorer ->
      Prims.bool ->
        Prims.bool ->
          FStar_InteractiveHelpers_Base.genv ->
            (FStar_InteractiveHelpers_Base.genv *
              FStar_Reflection_Data.term_view) Prims.list ->
              FStar_InteractiveHelpers_ExploreTerm.typ_or_comp
                FStar_Pervasives_Native.option ->
                FStar_Reflection_Types.term ->
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
                FStar_Tactics_Effect.tac_bind
                  (Prims.mk_range "FStar.InteractiveHelpers.PostProcess.fst"
                     (Prims.of_int (122)) (Prims.of_int (6))
                     (Prims.of_int (124)) (Prims.of_int (39)))
                  (Prims.mk_range "FStar.InteractiveHelpers.PostProcess.fst"
                     (Prims.of_int (122)) (Prims.of_int (2))
                     (Prims.of_int (124)) (Prims.of_int (39)))
                  (Obj.magic
                     (FStar_InteractiveHelpers_ExploreTerm.explore_term dbg
                        dfs ()
                        (Obj.magic (find_predicated_term_explorer pred dbg))
                        (Obj.magic FStar_Pervasives_Native.None) ge pl opt_c
                        t))
                  (fun uu___ ->
                     FStar_Tactics_Effect.lift_div_tac
                       (fun uu___1 -> FStar_Pervasives_Native.fst uu___))
let (_is_focused_term_explorer : FStar_Reflection_Types.term pred_explorer) =
  fun ge -> fun pl -> fun opt_c -> fun tv -> is_focused_term tv
let (find_focused_term :
  Prims.bool ->
    Prims.bool ->
      FStar_InteractiveHelpers_Base.genv ->
        (FStar_InteractiveHelpers_Base.genv *
          FStar_Reflection_Data.term_view) Prims.list ->
          FStar_InteractiveHelpers_ExploreTerm.typ_or_comp
            FStar_Pervasives_Native.option ->
            FStar_Reflection_Types.term ->
              (FStar_Reflection_Types.term exploration_result
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
    (FStar_Reflection_Types.term exploration_result, unit)
      FStar_Tactics_Effect.tac_repr)
  =
  fun dbg ->
    FStar_Tactics_Effect.tac_bind
      (Prims.mk_range "FStar.InteractiveHelpers.PostProcess.fst"
         (Prims.of_int (138)) (Prims.of_int (10)) (Prims.of_int (138))
         (Prims.of_int (21)))
      (Prims.mk_range "FStar.InteractiveHelpers.PostProcess.fst"
         (Prims.of_int (139)) (Prims.of_int (2)) (Prims.of_int (155))
         (Prims.of_int (5))) (Obj.magic (FStar_Tactics_Derived.cur_goal ()))
      (fun uu___ ->
         (fun g ->
            Obj.magic
              (FStar_Tactics_Effect.tac_bind
                 (Prims.mk_range "FStar.InteractiveHelpers.PostProcess.fst"
                    (Prims.of_int (139)) (Prims.of_int (10))
                    (Prims.of_int (139)) (Prims.of_int (20)))
                 (Prims.mk_range "FStar.InteractiveHelpers.PostProcess.fst"
                    (Prims.of_int (140)) (Prims.of_int (2))
                    (Prims.of_int (155)) (Prims.of_int (5)))
                 (Obj.magic (FStar_Tactics_Derived.cur_env ()))
                 (fun uu___ ->
                    (fun e ->
                       Obj.magic
                         (FStar_Tactics_Effect.tac_bind
                            (Prims.mk_range
                               "FStar.InteractiveHelpers.PostProcess.fst"
                               (Prims.of_int (140)) (Prims.of_int (2))
                               (Prims.of_int (140)) (Prims.of_int (80)))
                            (Prims.mk_range
                               "FStar.InteractiveHelpers.PostProcess.fst"
                               (Prims.of_int (141)) (Prims.of_int (8))
                               (Prims.of_int (154)) (Prims.of_int (75)))
                            (Obj.magic
                               (FStar_Tactics_Effect.tac_bind
                                  (Prims.mk_range
                                     "FStar.InteractiveHelpers.PostProcess.fst"
                                     (Prims.of_int (140)) (Prims.of_int (16))
                                     (Prims.of_int (140)) (Prims.of_int (80)))
                                  (Prims.mk_range
                                     "FStar.InteractiveHelpers.PostProcess.fst"
                                     (Prims.of_int (140)) (Prims.of_int (2))
                                     (Prims.of_int (140)) (Prims.of_int (80)))
                                  (Obj.magic
                                     (FStar_Tactics_Effect.tac_bind
                                        (Prims.mk_range
                                           "FStar.InteractiveHelpers.PostProcess.fst"
                                           (Prims.of_int (140))
                                           (Prims.of_int (63))
                                           (Prims.of_int (140))
                                           (Prims.of_int (79)))
                                        (Prims.mk_range "prims.fst"
                                           (Prims.of_int (606))
                                           (Prims.of_int (19))
                                           (Prims.of_int (606))
                                           (Prims.of_int (31)))
                                        (Obj.magic
                                           (FStar_Tactics_Builtins.term_to_string
                                              g))
                                        (fun uu___ ->
                                           FStar_Tactics_Effect.lift_div_tac
                                             (fun uu___1 ->
                                                Prims.strcat
                                                  "[> find_focused_assert_in_current_goal:\n"
                                                  uu___))))
                                  (fun uu___ ->
                                     (fun uu___ ->
                                        Obj.magic
                                          (FStar_InteractiveHelpers_Base.print_dbg
                                             dbg uu___)) uu___)))
                            (fun uu___ ->
                               (fun uu___ ->
                                  Obj.magic
                                    (FStar_Tactics_Effect.tac_bind
                                       (Prims.mk_range
                                          "FStar.InteractiveHelpers.PostProcess.fst"
                                          (Prims.of_int (141))
                                          (Prims.of_int (14))
                                          (Prims.of_int (141))
                                          (Prims.of_int (33)))
                                       (Prims.mk_range
                                          "FStar.InteractiveHelpers.PostProcess.fst"
                                          (Prims.of_int (141))
                                          (Prims.of_int (8))
                                          (Prims.of_int (154))
                                          (Prims.of_int (75)))
                                       (Obj.magic (unsquash_equality g))
                                       (fun uu___1 ->
                                          (fun uu___1 ->
                                             match uu___1 with
                                             | FStar_Pervasives_Native.Some
                                                 (l, uu___2) ->
                                                 Obj.magic
                                                   (FStar_Tactics_Effect.tac_bind
                                                      (Prims.mk_range
                                                         "FStar.InteractiveHelpers.PostProcess.fst"
                                                         (Prims.of_int (143))
                                                         (Prims.of_int (12))
                                                         (Prims.of_int (143))
                                                         (Prims.of_int (36)))
                                                      (Prims.mk_range
                                                         "FStar.InteractiveHelpers.PostProcess.fst"
                                                         (Prims.of_int (144))
                                                         (Prims.of_int (4))
                                                         (Prims.of_int (153))
                                                         (Prims.of_int (7)))
                                                      (Obj.magic
                                                         (FStar_InteractiveHelpers_ExploreTerm.safe_typ_or_comp
                                                            dbg e l))
                                                      (fun uu___3 ->
                                                         (fun c ->
                                                            Obj.magic
                                                              (FStar_Tactics_Effect.tac_bind
                                                                 (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (144))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (144))
                                                                    (Prims.of_int (28)))
                                                                 (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (145))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (153))
                                                                    (Prims.of_int (7)))
                                                                 (FStar_Tactics_Effect.lift_div_tac
                                                                    (
                                                                    fun
                                                                    uu___3 ->
                                                                    FStar_InteractiveHelpers_Base.mk_genv
                                                                    e [] []))
                                                                 (fun uu___3
                                                                    ->
                                                                    (fun ge
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (145))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (145))
                                                                    (Prims.of_int (68)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (146))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (152))
                                                                    (Prims.of_int (32)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (145))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (145))
                                                                    (Prims.of_int (68)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (145))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (145))
                                                                    (Prims.of_int (68)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (145))
                                                                    (Prims.of_int (51))
                                                                    (Prims.of_int (145))
                                                                    (Prims.of_int (67)))
                                                                    (Prims.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (606))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (606))
                                                                    (Prims.of_int (31)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Builtins.term_to_string
                                                                    l))
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    Prims.strcat
                                                                    "[> About to explore term:\n"
                                                                    uu___3))))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    uu___3))
                                                                    uu___3)))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (146))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (146))
                                                                    (Prims.of_int (52)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (146))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (152))
                                                                    (Prims.of_int (32)))
                                                                    (Obj.magic
                                                                    (find_focused_term
                                                                    dbg true
                                                                    ge [] c l))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    match uu___4
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    res ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (148))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (148))
                                                                    (Prims.of_int (73)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (147))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (147))
                                                                    (Prims.of_int (14)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (148))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (148))
                                                                    (Prims.of_int (73)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (148))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (148))
                                                                    (Prims.of_int (73)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (148))
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (148))
                                                                    (Prims.of_int (72)))
                                                                    (Prims.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (606))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (606))
                                                                    (Prims.of_int (31)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Builtins.term_to_string
                                                                    res.res))
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    Prims.strcat
                                                                    "[> Found focused term:\n"
                                                                    uu___5))))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    uu___5))
                                                                    uu___5)))
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    res)))
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (151))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (152))
                                                                    (Prims.of_int (32)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (151))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (152))
                                                                    (Prims.of_int (32)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (152))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (152))
                                                                    (Prims.of_int (31)))
                                                                    (Prims.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (606))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (606))
                                                                    (Prims.of_int (31)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Builtins.term_to_string
                                                                    g))
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    Prims.strcat
                                                                    "find_focused_term_in_current_goal: could not find a focused term in the current goal: "
                                                                    uu___5))))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.mfail
                                                                    uu___5))
                                                                    uu___5)))
                                                                    uu___4)))
                                                                    uu___3)))
                                                                    uu___3)))
                                                           uu___3))
                                             | uu___2 ->
                                                 Obj.magic
                                                   (FStar_InteractiveHelpers_Base.mfail
                                                      "find_focused_term_in_current_goal: not a squashed equality"))
                                            uu___1))) uu___))) uu___))) uu___)
let (find_focused_assert_in_current_goal :
  Prims.bool ->
    (FStar_Reflection_Types.term exploration_result, unit)
      FStar_Tactics_Effect.tac_repr)
  =
  fun dbg ->
    FStar_Tactics_Effect.tac_bind
      (Prims.mk_range "FStar.InteractiveHelpers.PostProcess.fst"
         (Prims.of_int (160)) (Prims.of_int (2)) (Prims.of_int (160))
         (Prims.of_int (58)))
      (Prims.mk_range "FStar.InteractiveHelpers.PostProcess.fst"
         (Prims.of_int (161)) (Prims.of_int (2)) (Prims.of_int (174))
         (Prims.of_int (5)))
      (Obj.magic
         (FStar_InteractiveHelpers_Base.print_dbg dbg
            "[> find_focused_assert_in_current_goal"))
      (fun uu___ ->
         (fun uu___ ->
            Obj.magic
              (FStar_Tactics_Effect.tac_bind
                 (Prims.mk_range "FStar.InteractiveHelpers.PostProcess.fst"
                    (Prims.of_int (161)) (Prims.of_int (12))
                    (Prims.of_int (161)) (Prims.of_int (49)))
                 (Prims.mk_range "FStar.InteractiveHelpers.PostProcess.fst"
                    (Prims.of_int (162)) (Prims.of_int (2))
                    (Prims.of_int (174)) (Prims.of_int (5)))
                 (Obj.magic (find_focused_term_in_current_goal dbg))
                 (fun uu___1 ->
                    (fun res ->
                       Obj.magic
                         (FStar_Tactics_Effect.tac_bind
                            (Prims.mk_range
                               "FStar.InteractiveHelpers.PostProcess.fst"
                               (Prims.of_int (162)) (Prims.of_int (2))
                               (Prims.of_int (162)) (Prims.of_int (69)))
                            (Prims.mk_range
                               "FStar.InteractiveHelpers.PostProcess.fst"
                               (Prims.of_int (164)) (Prims.of_int (2))
                               (Prims.of_int (174)) (Prims.of_int (5)))
                            (Obj.magic
                               (FStar_Tactics_Effect.tac_bind
                                  (Prims.mk_range
                                     "FStar.InteractiveHelpers.PostProcess.fst"
                                     (Prims.of_int (162)) (Prims.of_int (16))
                                     (Prims.of_int (162)) (Prims.of_int (69)))
                                  (Prims.mk_range
                                     "FStar.InteractiveHelpers.PostProcess.fst"
                                     (Prims.of_int (162)) (Prims.of_int (2))
                                     (Prims.of_int (162)) (Prims.of_int (69)))
                                  (Obj.magic
                                     (FStar_Tactics_Effect.tac_bind
                                        (Prims.mk_range
                                           "FStar.InteractiveHelpers.PostProcess.fst"
                                           (Prims.of_int (162))
                                           (Prims.of_int (46))
                                           (Prims.of_int (162))
                                           (Prims.of_int (68)))
                                        (Prims.mk_range "prims.fst"
                                           (Prims.of_int (606))
                                           (Prims.of_int (19))
                                           (Prims.of_int (606))
                                           (Prims.of_int (31)))
                                        (Obj.magic
                                           (FStar_Tactics_Builtins.term_to_string
                                              res.res))
                                        (fun uu___1 ->
                                           FStar_Tactics_Effect.lift_div_tac
                                             (fun uu___2 ->
                                                Prims.strcat
                                                  "[> Found focused term:\n"
                                                  uu___1))))
                                  (fun uu___1 ->
                                     (fun uu___1 ->
                                        Obj.magic
                                          (FStar_InteractiveHelpers_Base.print_dbg
                                             dbg uu___1)) uu___1)))
                            (fun uu___1 ->
                               (fun uu___1 ->
                                  Obj.magic
                                    (FStar_Tactics_Effect.tac_bind
                                       (Prims.mk_range
                                          "FStar.InteractiveHelpers.PostProcess.fst"
                                          (Prims.of_int (165))
                                          (Prims.of_int (4))
                                          (Prims.of_int (169))
                                          (Prims.of_int (14)))
                                       (Prims.mk_range
                                          "FStar.InteractiveHelpers.PostProcess.fst"
                                          (Prims.of_int (171))
                                          (Prims.of_int (8))
                                          (Prims.of_int (173))
                                          (Prims.of_int (38)))
                                       (Obj.magic
                                          (FStar_Tactics_Effect.tac_bind
                                             (Prims.mk_range
                                                "FStar.InteractiveHelpers.PostProcess.fst"
                                                (Prims.of_int (165))
                                                (Prims.of_int (10))
                                                (Prims.of_int (165))
                                                (Prims.of_int (25)))
                                             (Prims.mk_range
                                                "FStar.InteractiveHelpers.PostProcess.fst"
                                                (Prims.of_int (165))
                                                (Prims.of_int (4))
                                                (Prims.of_int (169))
                                                (Prims.of_int (14)))
                                             (Obj.magic
                                                (FStar_Tactics_Builtins.inspect
                                                   res.res))
                                             (fun uu___2 ->
                                                (fun uu___2 ->
                                                   match uu___2 with
                                                   | FStar_Reflection_Data.Tv_Let
                                                       (uu___3, uu___4, bv0,
                                                        fterm, uu___5)
                                                       ->
                                                       Obj.magic
                                                         (Obj.repr
                                                            (FStar_Tactics_Effect.tac_bind
                                                               (Prims.mk_range
                                                                  "FStar.InteractiveHelpers.PostProcess.fst"
                                                                  (Prims.of_int (167))
                                                                  (Prims.of_int (16))
                                                                  (Prims.of_int (167))
                                                                  (Prims.of_int (50)))
                                                               (Prims.mk_range
                                                                  "FStar.InteractiveHelpers.PostProcess.fst"
                                                                  (Prims.of_int (168))
                                                                  (Prims.of_int (6))
                                                                  (Prims.of_int (168))
                                                                  (Prims.of_int (42)))
                                                               (Obj.magic
                                                                  (FStar_InteractiveHelpers_Base.genv_push_bv
                                                                    res.ge
                                                                    bv0 false
                                                                    FStar_Pervasives_Native.None))
                                                               (fun ge' ->
                                                                  FStar_Tactics_Effect.lift_div_tac
                                                                    (
                                                                    fun
                                                                    uu___6 ->
                                                                    {
                                                                    ge = ge';
                                                                    parents =
                                                                    (res.parents);
                                                                    tgt_comp
                                                                    =
                                                                    (res.tgt_comp);
                                                                    res =
                                                                    fterm
                                                                    }))))
                                                   | uu___3 ->
                                                       Obj.magic
                                                         (Obj.repr
                                                            (FStar_Tactics_Effect.lift_div_tac
                                                               (fun uu___4 ->
                                                                  res))))
                                                  uu___2)))
                                       (fun uu___2 ->
                                          (fun res' ->
                                             Obj.magic
                                               (FStar_Tactics_Effect.tac_bind
                                                  (Prims.mk_range
                                                     "FStar.InteractiveHelpers.PostProcess.fst"
                                                     (Prims.of_int (171))
                                                     (Prims.of_int (14))
                                                     (Prims.of_int (171))
                                                     (Prims.of_int (47)))
                                                  (Prims.mk_range
                                                     "FStar.InteractiveHelpers.PostProcess.fst"
                                                     (Prims.of_int (171))
                                                     (Prims.of_int (8))
                                                     (Prims.of_int (173))
                                                     (Prims.of_int (38)))
                                                  (Obj.magic
                                                     (term_is_assert_or_assume
                                                        res'.res))
                                                  (fun uu___2 ->
                                                     (fun uu___2 ->
                                                        match uu___2 with
                                                        | FStar_Pervasives_Native.None
                                                            ->
                                                            Obj.magic
                                                              (Obj.repr
                                                                 (FStar_Tactics_Effect.tac_bind
                                                                    (
                                                                    Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (172))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (172))
                                                                    (Prims.of_int (144)))
                                                                    (
                                                                    Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (172))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (172))
                                                                    (Prims.of_int (144)))
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (172))
                                                                    (Prims.of_int (121))
                                                                    (Prims.of_int (172))
                                                                    (Prims.of_int (143)))
                                                                    (Prims.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (606))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (606))
                                                                    (Prims.of_int (31)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Builtins.term_to_string
                                                                    res.res))
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    Prims.strcat
                                                                    "find_focused_assert_in_current_goal: the found focused term is not an assertion or an assumption:"
                                                                    uu___3))))
                                                                    (
                                                                    fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.mfail
                                                                    uu___3))
                                                                    uu___3)))
                                                        | FStar_Pervasives_Native.Some
                                                            tm ->
                                                            Obj.magic
                                                              (Obj.repr
                                                                 (FStar_Tactics_Effect.lift_div_tac
                                                                    (
                                                                    fun
                                                                    uu___3 ->
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
                                                       uu___2))) uu___2)))
                                 uu___1))) uu___1))) uu___)
let (analyze_effectful_term :
  Prims.bool ->
    Prims.bool ->
      Prims.bool ->
        FStar_Reflection_Types.term exploration_result ->
          (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun dbg ->
    fun with_gpre ->
      fun with_gpost ->
        fun res ->
          FStar_Tactics_Effect.tac_bind
            (Prims.mk_range "FStar.InteractiveHelpers.PostProcess.fst"
               (Prims.of_int (190)) (Prims.of_int (11)) (Prims.of_int (190))
               (Prims.of_int (17)))
            (Prims.mk_range "FStar.InteractiveHelpers.PostProcess.fst"
               (Prims.of_int (191)) (Prims.of_int (2)) (Prims.of_int (247))
               (Prims.of_int (30)))
            (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> res.ge))
            (fun uu___ ->
               (fun ge ->
                  Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (Prims.mk_range
                          "FStar.InteractiveHelpers.PostProcess.fst"
                          (Prims.of_int (191)) (Prims.of_int (14))
                          (Prims.of_int (191)) (Prims.of_int (26)))
                       (Prims.mk_range
                          "FStar.InteractiveHelpers.PostProcess.fst"
                          (Prims.of_int (193)) (Prims.of_int (2))
                          (Prims.of_int (247)) (Prims.of_int (30)))
                       (FStar_Tactics_Effect.lift_div_tac
                          (fun uu___ -> res.tgt_comp))
                       (fun uu___ ->
                          (fun opt_c ->
                             Obj.magic
                               (FStar_Tactics_Effect.tac_bind
                                  (Prims.mk_range
                                     "FStar.InteractiveHelpers.PostProcess.fst"
                                     (Prims.of_int (194)) (Prims.of_int (10))
                                     (Prims.of_int (221)) (Prims.of_int (82)))
                                  (Prims.mk_range
                                     "FStar.InteractiveHelpers.PostProcess.fst"
                                     (Prims.of_int (193)) (Prims.of_int (2))
                                     (Prims.of_int (247)) (Prims.of_int (30)))
                                  (Obj.magic
                                     (FStar_Tactics_Effect.tac_bind
                                        (Prims.mk_range
                                           "FStar.InteractiveHelpers.PostProcess.fst"
                                           (Prims.of_int (194))
                                           (Prims.of_int (16))
                                           (Prims.of_int (194))
                                           (Prims.of_int (31)))
                                        (Prims.mk_range
                                           "FStar.InteractiveHelpers.PostProcess.fst"
                                           (Prims.of_int (194))
                                           (Prims.of_int (10))
                                           (Prims.of_int (221))
                                           (Prims.of_int (82)))
                                        (Obj.magic
                                           (FStar_Tactics_Builtins.inspect
                                              res.res))
                                        (fun uu___ ->
                                           (fun uu___ ->
                                              match uu___ with
                                              | FStar_Reflection_Data.Tv_Let
                                                  (uu___1, uu___2, bv0,
                                                   fterm, uu___3)
                                                  ->
                                                  Obj.magic
                                                    (FStar_Tactics_Effect.tac_bind
                                                       (Prims.mk_range
                                                          "FStar.InteractiveHelpers.PostProcess.fst"
                                                          (Prims.of_int (201))
                                                          (Prims.of_int (6))
                                                          (Prims.of_int (201))
                                                          (Prims.of_int (63)))
                                                       (Prims.mk_range
                                                          "FStar.InteractiveHelpers.PostProcess.fst"
                                                          (Prims.of_int (202))
                                                          (Prims.of_int (6))
                                                          (Prims.of_int (220))
                                                          (Prims.of_int (69)))
                                                       (Obj.magic
                                                          (FStar_Tactics_Effect.tac_bind
                                                             (Prims.mk_range
                                                                "FStar.InteractiveHelpers.PostProcess.fst"
                                                                (Prims.of_int (201))
                                                                (Prims.of_int (20))
                                                                (Prims.of_int (201))
                                                                (Prims.of_int (63)))
                                                             (Prims.mk_range
                                                                "FStar.InteractiveHelpers.PostProcess.fst"
                                                                (Prims.of_int (201))
                                                                (Prims.of_int (6))
                                                                (Prims.of_int (201))
                                                                (Prims.of_int (63)))
                                                             (Obj.magic
                                                                (FStar_Tactics_Effect.tac_bind
                                                                   (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (201))
                                                                    (Prims.of_int (42))
                                                                    (Prims.of_int (201))
                                                                    (Prims.of_int (62)))
                                                                   (Prims.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (606))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (606))
                                                                    (Prims.of_int (31)))
                                                                   (Obj.magic
                                                                    (FStar_Tactics_Builtins.term_to_string
                                                                    fterm))
                                                                   (fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    Prims.strcat
                                                                    "Restraining to: "
                                                                    uu___4))))
                                                             (fun uu___4 ->
                                                                (fun uu___4
                                                                   ->
                                                                   Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    uu___4))
                                                                  uu___4)))
                                                       (fun uu___4 ->
                                                          (fun uu___4 ->
                                                             Obj.magic
                                                               (FStar_Tactics_Effect.tac_bind
                                                                  (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (203))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (205))
                                                                    (Prims.of_int (35)))
                                                                  (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (207))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (220))
                                                                    (Prims.of_int (69)))
                                                                  (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (203))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (203))
                                                                    (Prims.of_int (52)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (203))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (205))
                                                                    (Prims.of_int (35)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (203))
                                                                    (Prims.of_int (36))
                                                                    (Prims.of_int (203))
                                                                    (Prims.of_int (52)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (203))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (203))
                                                                    (Prims.of_int (52)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Derived.name_of_bv
                                                                    bv0))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.genv_get_from_name
                                                                    ge uu___5))
                                                                    uu___5)))
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    match uu___5
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    FStar_Pervasives_Native.None
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (sbv,
                                                                    uu___7)
                                                                    ->
                                                                    FStar_Pervasives_Native.Some
                                                                    sbv))))
                                                                  (fun uu___5
                                                                    ->
                                                                    (fun
                                                                    shadowed_bv
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (207))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (207))
                                                                    (Prims.of_int (46)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (212))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (220))
                                                                    (Prims.of_int (69)))
                                                                    (Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.genv_push_bv
                                                                    ge bv0
                                                                    false
                                                                    FStar_Pervasives_Native.None))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun ge1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (213))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (217))
                                                                    (Prims.of_int (21)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (212))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (220))
                                                                    (Prims.of_int (69)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (213))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (213))
                                                                    (Prims.of_int (33)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (214))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (217))
                                                                    (Prims.of_int (21)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Reflection_Builtins.inspect_bv
                                                                    bv0))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun bvv0
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (214))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (214))
                                                                    (Prims.of_int (77)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (215))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (217))
                                                                    (Prims.of_int (21)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (214))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (214))
                                                                    (Prims.of_int (77)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (214))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (214))
                                                                    (Prims.of_int (77)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (214))
                                                                    (Prims.of_int (59))
                                                                    (Prims.of_int (214))
                                                                    (Prims.of_int (76)))
                                                                    (Prims.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (606))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (606))
                                                                    (Prims.of_int (31)))
                                                                    (Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.abv_to_string
                                                                    bv0))
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    Prims.strcat
                                                                    "Variable bound in let: "
                                                                    uu___5))))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    uu___5))
                                                                    uu___5)))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (215))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (215))
                                                                    (Prims.of_int (42)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (215))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (217))
                                                                    (Prims.of_int (21)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (215))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (215))
                                                                    (Prims.of_int (32)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (215))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (215))
                                                                    (Prims.of_int (42)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Builtins.unseal
                                                                    bvv0.FStar_Reflection_Data.bv_ppname))
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    uu___6 =
                                                                    "uu___"))))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    uu___6 ->
                                                                    if uu___6
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_InteractiveHelpers_Base.genv_push_fresh_bv
                                                                    ge1 "ret"
                                                                    bvv0.FStar_Reflection_Data.bv_sort))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    (ge1,
                                                                    bv0)))))
                                                                    uu___6)))
                                                                    uu___5)))
                                                                    uu___5)))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    match uu___5
                                                                    with
                                                                    | 
                                                                    (ge2,
                                                                    bv1) ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (219))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (220))
                                                                    (Prims.of_int (69)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (219))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (220))
                                                                    (Prims.of_int (69)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    bv1))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun bv11
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (219))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (219))
                                                                    (Prims.of_int (53)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (220))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (220))
                                                                    (Prims.of_int (69)))
                                                                    (Obj.magic
                                                                    (FStar_InteractiveHelpers_Effectful.compute_eterm_info
                                                                    dbg
                                                                    ge2.FStar_InteractiveHelpers_Base.env
                                                                    fterm))
                                                                    (fun info
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    (ge2,
                                                                    fterm,
                                                                    info,
                                                                    (FStar_Pervasives_Native.Some
                                                                    bv11),
                                                                    shadowed_bv,
                                                                    true)))))
                                                                    uu___6)))
                                                                    uu___5)))
                                                                    uu___5)))
                                                                    uu___5)))
                                                            uu___4))
                                              | uu___1 ->
                                                  Obj.magic
                                                    (FStar_Tactics_Effect.tac_bind
                                                       (Prims.mk_range
                                                          "FStar.InteractiveHelpers.PostProcess.fst"
                                                          (Prims.of_int (221))
                                                          (Prims.of_int (25))
                                                          (Prims.of_int (221))
                                                          (Prims.of_int (62)))
                                                       (Prims.mk_range
                                                          "FStar.InteractiveHelpers.PostProcess.fst"
                                                          (Prims.of_int (221))
                                                          (Prims.of_int (11))
                                                          (Prims.of_int (221))
                                                          (Prims.of_int (82)))
                                                       (Obj.magic
                                                          (FStar_InteractiveHelpers_Effectful.compute_eterm_info
                                                             dbg
                                                             ge.FStar_InteractiveHelpers_Base.env
                                                             res.res))
                                                       (fun uu___2 ->
                                                          FStar_Tactics_Effect.lift_div_tac
                                                            (fun uu___3 ->
                                                               (ge,
                                                                 (res.res),
                                                                 uu___2,
                                                                 FStar_Pervasives_Native.None,
                                                                 FStar_Pervasives_Native.None,
                                                                 false)))))
                                             uu___)))
                                  (fun uu___ ->
                                     (fun uu___ ->
                                        match uu___ with
                                        | (ge1, studied_term, info, ret_bv,
                                           shadowed_bv, is_let) ->
                                            Obj.magic
                                              (FStar_Tactics_Effect.tac_bind
                                                 (Prims.mk_range
                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                    (Prims.of_int (224))
                                                    (Prims.of_int (2))
                                                    (Prims.of_int (224))
                                                    (Prims.of_int (79)))
                                                 (Prims.mk_range
                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                    (Prims.of_int (225))
                                                    (Prims.of_int (2))
                                                    (Prims.of_int (247))
                                                    (Prims.of_int (30)))
                                                 (Obj.magic
                                                    (FStar_Tactics_Effect.tac_bind
                                                       (Prims.mk_range
                                                          "FStar.InteractiveHelpers.PostProcess.fst"
                                                          (Prims.of_int (224))
                                                          (Prims.of_int (16))
                                                          (Prims.of_int (224))
                                                          (Prims.of_int (79)))
                                                       (Prims.mk_range
                                                          "FStar.InteractiveHelpers.PostProcess.fst"
                                                          (Prims.of_int (224))
                                                          (Prims.of_int (2))
                                                          (Prims.of_int (224))
                                                          (Prims.of_int (79)))
                                                       (Obj.magic
                                                          (FStar_Tactics_Effect.tac_bind
                                                             (Prims.mk_range
                                                                "FStar.InteractiveHelpers.PostProcess.fst"
                                                                (Prims.of_int (224))
                                                                (Prims.of_int (51))
                                                                (Prims.of_int (224))
                                                                (Prims.of_int (78)))
                                                             (Prims.mk_range
                                                                "prims.fst"
                                                                (Prims.of_int (606))
                                                                (Prims.of_int (19))
                                                                (Prims.of_int (606))
                                                                (Prims.of_int (31)))
                                                             (Obj.magic
                                                                (FStar_InteractiveHelpers_Base.term_construct
                                                                   studied_term))
                                                             (fun uu___1 ->
                                                                FStar_Tactics_Effect.lift_div_tac
                                                                  (fun uu___2
                                                                    ->
                                                                    Prims.strcat
                                                                    "[> Focused term constructor: "
                                                                    uu___1))))
                                                       (fun uu___1 ->
                                                          (fun uu___1 ->
                                                             Obj.magic
                                                               (FStar_InteractiveHelpers_Base.print_dbg
                                                                  dbg uu___1))
                                                            uu___1)))
                                                 (fun uu___1 ->
                                                    (fun uu___1 ->
                                                       Obj.magic
                                                         (FStar_Tactics_Effect.tac_bind
                                                            (Prims.mk_range
                                                               "FStar.InteractiveHelpers.PostProcess.fst"
                                                               (Prims.of_int (225))
                                                               (Prims.of_int (2))
                                                               (Prims.of_int (225))
                                                               (Prims.of_int (94)))
                                                            (Prims.mk_range
                                                               "FStar.InteractiveHelpers.PostProcess.fst"
                                                               (Prims.of_int (229))
                                                               (Prims.of_int (2))
                                                               (Prims.of_int (247))
                                                               (Prims.of_int (30)))
                                                            (Obj.magic
                                                               (FStar_Tactics_Effect.tac_bind
                                                                  (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (225))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (225))
                                                                    (Prims.of_int (94)))
                                                                  (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (225))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (225))
                                                                    (Prims.of_int (94)))
                                                                  (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (225))
                                                                    (Prims.of_int (75))
                                                                    (Prims.of_int (225))
                                                                    (Prims.of_int (93)))
                                                                    (Prims.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (606))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (606))
                                                                    (Prims.of_int (31)))
                                                                    (Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.genv_to_string
                                                                    ge1))
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    Prims.strcat
                                                                    "[> Environment information (after effect analysis):\n"
                                                                    uu___2))))
                                                                  (fun uu___2
                                                                    ->
                                                                    (fun
                                                                    uu___2 ->
                                                                    Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    uu___2))
                                                                    uu___2)))
                                                            (fun uu___2 ->
                                                               (fun uu___2 ->
                                                                  Obj.magic
                                                                    (
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (229))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (229))
                                                                    (Prims.of_int (63)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (232))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (247))
                                                                    (Prims.of_int (30)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (229))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (229))
                                                                    (Prims.of_int (63)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (229))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (229))
                                                                    (Prims.of_int (63)))
                                                                    (Obj.magic
                                                                    (term_is_assert_or_assume
                                                                    studied_term))
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Pervasives_Native.uu___is_Some
                                                                    uu___3))))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    is_assert
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (232))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (232))
                                                                    (Prims.of_int (60)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (233))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (247))
                                                                    (Prims.of_int (30)))
                                                                    (Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.opt_tapply
                                                                    (fun x ->
                                                                    FStar_Tactics_Builtins.pack
                                                                    (FStar_Reflection_Data.Tv_Var
                                                                    x))
                                                                    ret_bv))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    ret_arg
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (233))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (233))
                                                                    (Prims.of_int (44)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (234))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (247))
                                                                    (Prims.of_int (30)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_List_Tot_Base.map
                                                                    FStar_Pervasives_Native.snd
                                                                    res.parents))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    parents
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (235))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (236))
                                                                    (Prims.of_int (68)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (234))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (247))
                                                                    (Prims.of_int (30)))
                                                                    (Obj.magic
                                                                    (FStar_InteractiveHelpers_Effectful.eterm_info_to_assertions
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
                                                                    []))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    match uu___3
                                                                    with
                                                                    | 
                                                                    (ge2,
                                                                    asserts)
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (238))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (238))
                                                                    (Prims.of_int (71)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (240))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (247))
                                                                    (Prims.of_int (30)))
                                                                    (Obj.magic
                                                                    (FStar_InteractiveHelpers_Propositions.simp_filter_assertions
                                                                    ge2.FStar_InteractiveHelpers_Base.env
                                                                    FStar_InteractiveHelpers_Propositions.simpl_norm_steps
                                                                    asserts))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    asserts1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (240))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (240))
                                                                    (Prims.of_int (86)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (240))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (247))
                                                                    (Prims.of_int (30)))
                                                                    (Obj.magic
                                                                    (FStar_InteractiveHelpers_Output.subst_shadowed_with_abs_in_assertions
                                                                    dbg ge2
                                                                    shadowed_bv
                                                                    asserts1))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    match uu___4
                                                                    with
                                                                    | 
                                                                    (ge3,
                                                                    asserts2)
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (243))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (244))
                                                                    (Prims.of_int (70)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (247))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (247))
                                                                    (Prims.of_int (30)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    if is_let
                                                                    then
                                                                    asserts2
                                                                    else
                                                                    FStar_InteractiveHelpers_Propositions.mk_assertions
                                                                    (FStar_List_Tot_Base.append
                                                                    asserts2.FStar_InteractiveHelpers_Propositions.pres
                                                                    asserts2.FStar_InteractiveHelpers_Propositions.posts)
                                                                    []))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    asserts3
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_InteractiveHelpers_Output.printout_success
                                                                    ge3
                                                                    asserts3))
                                                                    uu___5)))
                                                                    uu___4)))
                                                                    uu___4)))
                                                                    uu___3)))
                                                                    uu___3)))
                                                                    uu___3)))
                                                                    uu___3)))
                                                                 uu___2)))
                                                      uu___1))) uu___)))
                            uu___))) uu___)
let (pp_analyze_effectful_term :
  Prims.bool ->
    Prims.bool ->
      Prims.bool -> unit -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun dbg ->
    fun with_gpre ->
      fun with_gpost ->
        fun uu___ ->
          FStar_Tactics_Derived.try_with
            (fun uu___1 ->
               match () with
               | () ->
                   FStar_Tactics_Effect.tac_bind
                     (Prims.mk_range
                        "FStar.InteractiveHelpers.PostProcess.fst"
                        (Prims.of_int (253)) (Prims.of_int (14))
                        (Prims.of_int (253)) (Prims.of_int (51)))
                     (Prims.mk_range
                        "FStar.InteractiveHelpers.PostProcess.fst"
                        (Prims.of_int (254)) (Prims.of_int (4))
                        (Prims.of_int (255)) (Prims.of_int (16)))
                     (Obj.magic (find_focused_term_in_current_goal dbg))
                     (fun uu___2 ->
                        (fun res ->
                           Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (Prims.mk_range
                                   "FStar.InteractiveHelpers.PostProcess.fst"
                                   (Prims.of_int (254)) (Prims.of_int (4))
                                   (Prims.of_int (254)) (Prims.of_int (55)))
                                (Prims.mk_range
                                   "FStar.InteractiveHelpers.PostProcess.fst"
                                   (Prims.of_int (255)) (Prims.of_int (4))
                                   (Prims.of_int (255)) (Prims.of_int (16)))
                                (Obj.magic
                                   (analyze_effectful_term dbg with_gpre
                                      with_gpost res))
                                (fun uu___2 ->
                                   (fun uu___2 -> Obj.magic (end_proof ()))
                                     uu___2))) uu___2))
            (fun uu___1 ->
               match uu___1 with
               | FStar_InteractiveHelpers_Base.MetaAnalysis msg ->
                   FStar_Tactics_Effect.tac_bind
                     (Prims.mk_range
                        "FStar.InteractiveHelpers.PostProcess.fst"
                        (Prims.of_int (256)) (Prims.of_int (29))
                        (Prims.of_int (256)) (Prims.of_int (49)))
                     (Prims.mk_range
                        "FStar.InteractiveHelpers.PostProcess.fst"
                        (Prims.of_int (256)) (Prims.of_int (51))
                        (Prims.of_int (256)) (Prims.of_int (63)))
                     (Obj.magic
                        (FStar_InteractiveHelpers_Output.printout_failure msg))
                     (fun uu___2 ->
                        (fun uu___2 -> Obj.magic (end_proof ())) uu___2)
               | err -> FStar_Tactics_Effect.raise err)
let _ =
  FStar_Tactics_Native.register_tactic
    "FStar.InteractiveHelpers.PostProcess.pp_analyze_effectful_term"
    (Prims.of_int (5))
    (fun psc ->
       fun ncb ->
         fun args ->
           FStar_Tactics_InterpFuns.mk_tactic_interpretation_4
             (FStar_Tactics_Native.from_tactic_4 pp_analyze_effectful_term)
             FStar_Syntax_Embeddings.e_bool FStar_Syntax_Embeddings.e_bool
             FStar_Syntax_Embeddings.e_bool FStar_Syntax_Embeddings.e_unit
             FStar_Syntax_Embeddings.e_unit psc ncb args)
let (remove_b2t :
  FStar_Reflection_Types.term ->
    (FStar_Reflection_Types.term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    FStar_Tactics_Effect.tac_bind
      (Prims.mk_range "FStar.InteractiveHelpers.PostProcess.fst"
         (Prims.of_int (272)) (Prims.of_int (8)) (Prims.of_int (272))
         (Prims.of_int (17)))
      (Prims.mk_range "FStar.InteractiveHelpers.PostProcess.fst"
         (Prims.of_int (272)) (Prims.of_int (2)) (Prims.of_int (279))
         (Prims.of_int (10))) (Obj.magic (FStar_Tactics_Builtins.inspect t))
      (fun uu___ ->
         (fun uu___ ->
            match uu___ with
            | FStar_Reflection_Data.Tv_App
                (hd, (a, FStar_Reflection_Data.Q_Explicit)) ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.tac_bind
                        (Prims.mk_range
                           "FStar.InteractiveHelpers.PostProcess.fst"
                           (Prims.of_int (274)) (Prims.of_int (16))
                           (Prims.of_int (274)) (Prims.of_int (26)))
                        (Prims.mk_range
                           "FStar.InteractiveHelpers.PostProcess.fst"
                           (Prims.of_int (274)) (Prims.of_int (10))
                           (Prims.of_int (277)) (Prims.of_int (12)))
                        (Obj.magic (FStar_Tactics_Builtins.inspect hd))
                        (fun uu___1 ->
                           FStar_Tactics_Effect.lift_div_tac
                             (fun uu___2 ->
                                match uu___1 with
                                | FStar_Reflection_Data.Tv_FVar fv ->
                                    if
                                      FStar_InteractiveHelpers_Base.fv_eq_name
                                        fv FStar_Reflection_Const.b2t_qn
                                    then a
                                    else t
                                | uu___3 -> t))))
            | uu___1 ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.lift_div_tac (fun uu___2 -> t))))
           uu___)
let (is_conjunction :
  FStar_Reflection_Types.term ->
    ((FStar_Reflection_Types.term * FStar_Reflection_Types.term)
       FStar_Pervasives_Native.option,
      unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    FStar_Tactics_Effect.tac_bind
      (Prims.mk_range "FStar.InteractiveHelpers.PostProcess.fst"
         (Prims.of_int (285)) (Prims.of_int (10)) (Prims.of_int (285))
         (Prims.of_int (22)))
      (Prims.mk_range "FStar.InteractiveHelpers.PostProcess.fst"
         (Prims.of_int (286)) (Prims.of_int (2)) (Prims.of_int (296))
         (Prims.of_int (13))) (Obj.magic (remove_b2t t))
      (fun uu___ ->
         (fun t1 ->
            Obj.magic
              (FStar_Tactics_Effect.tac_bind
                 (Prims.mk_range "FStar.InteractiveHelpers.PostProcess.fst"
                    (Prims.of_int (286)) (Prims.of_int (19))
                    (Prims.of_int (286)) (Prims.of_int (32)))
                 (Prims.mk_range "FStar.InteractiveHelpers.PostProcess.fst"
                    (Prims.of_int (286)) (Prims.of_int (2))
                    (Prims.of_int (296)) (Prims.of_int (13)))
                 (FStar_Tactics_Effect.lift_div_tac
                    (fun uu___ -> FStar_Reflection_Derived.collect_app t1))
                 (fun uu___ ->
                    (fun uu___ ->
                       match uu___ with
                       | (hd, params) ->
                           (match params with
                            | (x, FStar_Reflection_Data.Q_Explicit)::
                                (y, FStar_Reflection_Data.Q_Explicit)::[] ->
                                Obj.magic
                                  (Obj.repr
                                     (FStar_Tactics_Effect.tac_bind
                                        (Prims.mk_range
                                           "FStar.InteractiveHelpers.PostProcess.fst"
                                           (Prims.of_int (289))
                                           (Prims.of_int (16))
                                           (Prims.of_int (289))
                                           (Prims.of_int (26)))
                                        (Prims.mk_range
                                           "FStar.InteractiveHelpers.PostProcess.fst"
                                           (Prims.of_int (289))
                                           (Prims.of_int (10))
                                           (Prims.of_int (294))
                                           (Prims.of_int (15)))
                                        (Obj.magic
                                           (FStar_Tactics_Builtins.inspect hd))
                                        (fun uu___1 ->
                                           FStar_Tactics_Effect.lift_div_tac
                                             (fun uu___2 ->
                                                match uu___1 with
                                                | FStar_Reflection_Data.Tv_FVar
                                                    fv ->
                                                    if
                                                      ((FStar_Reflection_Builtins.inspect_fv
                                                          fv)
                                                         =
                                                         FStar_Reflection_Const.and_qn)
                                                        ||
                                                        ((FStar_Reflection_Builtins.inspect_fv
                                                            fv)
                                                           =
                                                           ["Prims";
                                                           "op_AmpAmp"])
                                                    then
                                                      FStar_Pervasives_Native.Some
                                                        (x, y)
                                                    else
                                                      FStar_Pervasives_Native.None
                                                | uu___3 ->
                                                    FStar_Pervasives_Native.None))))
                            | uu___1 ->
                                Obj.magic
                                  (Obj.repr
                                     (FStar_Tactics_Effect.lift_div_tac
                                        (fun uu___2 ->
                                           FStar_Pervasives_Native.None)))))
                      uu___))) uu___)
let rec (_split_conjunctions :
  FStar_Reflection_Types.term Prims.list ->
    FStar_Reflection_Types.term ->
      (FStar_Reflection_Types.term Prims.list, unit)
        FStar_Tactics_Effect.tac_repr)
  =
  fun ls ->
    fun t ->
      FStar_Tactics_Effect.tac_bind
        (Prims.mk_range "FStar.InteractiveHelpers.PostProcess.fst"
           (Prims.of_int (301)) (Prims.of_int (8)) (Prims.of_int (301))
           (Prims.of_int (24)))
        (Prims.mk_range "FStar.InteractiveHelpers.PostProcess.fst"
           (Prims.of_int (301)) (Prims.of_int (2)) (Prims.of_int (306))
           (Prims.of_int (7))) (Obj.magic (is_conjunction t))
        (fun uu___ ->
           (fun uu___ ->
              match uu___ with
              | FStar_Pervasives_Native.None ->
                  Obj.magic
                    (Obj.repr
                       (FStar_Tactics_Effect.lift_div_tac
                          (fun uu___1 -> t :: ls)))
              | FStar_Pervasives_Native.Some (l, r) ->
                  Obj.magic
                    (Obj.repr
                       (FStar_Tactics_Effect.tac_bind
                          (Prims.mk_range
                             "FStar.InteractiveHelpers.PostProcess.fst"
                             (Prims.of_int (304)) (Prims.of_int (14))
                             (Prims.of_int (304)) (Prims.of_int (38)))
                          (Prims.mk_range
                             "FStar.InteractiveHelpers.PostProcess.fst"
                             (Prims.of_int (305)) (Prims.of_int (4))
                             (Prims.of_int (306)) (Prims.of_int (7)))
                          (Obj.magic (_split_conjunctions ls r))
                          (fun uu___1 ->
                             (fun ls1 ->
                                Obj.magic
                                  (FStar_Tactics_Effect.tac_bind
                                     (Prims.mk_range
                                        "FStar.InteractiveHelpers.PostProcess.fst"
                                        (Prims.of_int (305))
                                        (Prims.of_int (14))
                                        (Prims.of_int (305))
                                        (Prims.of_int (39)))
                                     (Prims.mk_range
                                        "FStar.InteractiveHelpers.PostProcess.fst"
                                        (Prims.of_int (305))
                                        (Prims.of_int (8))
                                        (Prims.of_int (305))
                                        (Prims.of_int (11)))
                                     (Obj.magic (_split_conjunctions ls1 l))
                                     (fun ls2 ->
                                        FStar_Tactics_Effect.lift_div_tac
                                          (fun uu___1 -> ls2)))) uu___1))))
             uu___)
let (split_conjunctions :
  FStar_Reflection_Types.term ->
    (FStar_Reflection_Types.term Prims.list, unit)
      FStar_Tactics_Effect.tac_repr)
  = fun t -> _split_conjunctions [] t
let (split_conjunctions_under_match :
  Prims.bool ->
    FStar_Reflection_Types.term ->
      (FStar_Reflection_Types.term Prims.list, unit)
        FStar_Tactics_Effect.tac_repr)
  =
  fun dbg ->
    fun t ->
      FStar_Tactics_Effect.tac_bind
        (Prims.mk_range "FStar.InteractiveHelpers.PostProcess.fst"
           (Prims.of_int (320)) (Prims.of_int (11)) (Prims.of_int (320))
           (Prims.of_int (23)))
        (Prims.mk_range "FStar.InteractiveHelpers.PostProcess.fst"
           (Prims.of_int (321)) (Prims.of_int (2)) (Prims.of_int (328))
           (Prims.of_int (7))) (Obj.magic (remove_b2t t))
        (fun uu___ ->
           (fun t1 ->
              Obj.magic
                (FStar_Tactics_Effect.tac_bind
                   (Prims.mk_range "FStar.InteractiveHelpers.PostProcess.fst"
                      (Prims.of_int (321)) (Prims.of_int (2))
                      (Prims.of_int (321)) (Prims.of_int (75)))
                   (Prims.mk_range "FStar.InteractiveHelpers.PostProcess.fst"
                      (Prims.of_int (322)) (Prims.of_int (2))
                      (Prims.of_int (328)) (Prims.of_int (7)))
                   (Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (Prims.mk_range
                            "FStar.InteractiveHelpers.PostProcess.fst"
                            (Prims.of_int (321)) (Prims.of_int (16))
                            (Prims.of_int (321)) (Prims.of_int (75)))
                         (Prims.mk_range
                            "FStar.InteractiveHelpers.PostProcess.fst"
                            (Prims.of_int (321)) (Prims.of_int (2))
                            (Prims.of_int (321)) (Prims.of_int (75)))
                         (Obj.magic
                            (FStar_Tactics_Effect.tac_bind
                               (Prims.mk_range
                                  "FStar.InteractiveHelpers.PostProcess.fst"
                                  (Prims.of_int (321)) (Prims.of_int (57))
                                  (Prims.of_int (321)) (Prims.of_int (74)))
                               (Prims.mk_range "prims.fst"
                                  (Prims.of_int (606)) (Prims.of_int (19))
                                  (Prims.of_int (606)) (Prims.of_int (31)))
                               (Obj.magic
                                  (FStar_InteractiveHelpers_Base.term_construct
                                     t1))
                               (fun uu___ ->
                                  FStar_Tactics_Effect.lift_div_tac
                                    (fun uu___1 ->
                                       Prims.strcat
                                         "[> split_conjunctions_under_match: "
                                         uu___))))
                         (fun uu___ ->
                            (fun uu___ ->
                               Obj.magic
                                 (FStar_InteractiveHelpers_Base.print_dbg dbg
                                    uu___)) uu___)))
                   (fun uu___ ->
                      (fun uu___ ->
                         Obj.magic
                           (FStar_Tactics_Effect.tac_bind
                              (Prims.mk_range
                                 "FStar.InteractiveHelpers.PostProcess.fst"
                                 (Prims.of_int (322)) (Prims.of_int (8))
                                 (Prims.of_int (322)) (Prims.of_int (18)))
                              (Prims.mk_range
                                 "FStar.InteractiveHelpers.PostProcess.fst"
                                 (Prims.of_int (322)) (Prims.of_int (2))
                                 (Prims.of_int (328)) (Prims.of_int (7)))
                              (Obj.magic (FStar_Tactics_Builtins.inspect t1))
                              (fun uu___1 ->
                                 (fun uu___1 ->
                                    match uu___1 with
                                    | FStar_Reflection_Data.Tv_Match
                                        (scrut, ret_opt, (pat, br)::[]) ->
                                        Obj.magic
                                          (Obj.repr
                                             (FStar_Tactics_Effect.tac_bind
                                                (Prims.mk_range
                                                   "FStar.InteractiveHelpers.PostProcess.fst"
                                                   (Prims.of_int (324))
                                                   (Prims.of_int (13))
                                                   (Prims.of_int (324))
                                                   (Prims.of_int (34)))
                                                (Prims.mk_range
                                                   "FStar.InteractiveHelpers.PostProcess.fst"
                                                   (Prims.of_int (325))
                                                   (Prims.of_int (4))
                                                   (Prims.of_int (325))
                                                   (Prims.of_int (62)))
                                                (Obj.magic
                                                   (split_conjunctions br))
                                                (fun uu___2 ->
                                                   (fun tl ->
                                                      Obj.magic
                                                        (FStar_Tactics_Util.map
                                                           (fun x ->
                                                              FStar_Tactics_Builtins.pack
                                                                (FStar_Reflection_Data.Tv_Match
                                                                   (scrut,
                                                                    ret_opt,
                                                                    [
                                                                    (pat, x)])))
                                                           tl)) uu___2)))
                                    | uu___2 ->
                                        Obj.magic
                                          (Obj.repr
                                             (FStar_Tactics_Effect.lift_div_tac
                                                (fun uu___3 -> [t])))) uu___1)))
                        uu___))) uu___)
let (split_assert_conjs :
  Prims.bool ->
    FStar_Reflection_Types.term exploration_result ->
      (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun dbg ->
    fun res ->
      FStar_Tactics_Effect.tac_bind
        (Prims.mk_range "FStar.InteractiveHelpers.PostProcess.fst"
           (Prims.of_int (332)) (Prims.of_int (12)) (Prims.of_int (332))
           (Prims.of_int (18)))
        (Prims.mk_range "FStar.InteractiveHelpers.PostProcess.fst"
           (Prims.of_int (334)) (Prims.of_int (2)) (Prims.of_int (347))
           (Prims.of_int (30)))
        (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> res.ge))
        (fun uu___ ->
           (fun ge0 ->
              Obj.magic
                (FStar_Tactics_Effect.tac_bind
                   (Prims.mk_range "FStar.InteractiveHelpers.PostProcess.fst"
                      (Prims.of_int (334)) (Prims.of_int (10))
                      (Prims.of_int (334)) (Prims.of_int (56)))
                   (Prims.mk_range "FStar.InteractiveHelpers.PostProcess.fst"
                      (Prims.of_int (336)) (Prims.of_int (2))
                      (Prims.of_int (347)) (Prims.of_int (30)))
                   (Obj.magic
                      (FStar_Tactics_Builtins.norm_term_env
                         ge0.FStar_InteractiveHelpers_Base.env
                         FStar_InteractiveHelpers_Propositions.simpl_norm_steps
                         res.res))
                   (fun uu___ ->
                      (fun t ->
                         Obj.magic
                           (FStar_Tactics_Effect.tac_bind
                              (Prims.mk_range
                                 "FStar.InteractiveHelpers.PostProcess.fst"
                                 (Prims.of_int (336)) (Prims.of_int (14))
                                 (Prims.of_int (336)) (Prims.of_int (34)))
                              (Prims.mk_range
                                 "FStar.InteractiveHelpers.PostProcess.fst"
                                 (Prims.of_int (341)) (Prims.of_int (2))
                                 (Prims.of_int (347)) (Prims.of_int (30)))
                              (Obj.magic (split_conjunctions t))
                              (fun uu___ ->
                                 (fun conjs ->
                                    Obj.magic
                                      (FStar_Tactics_Effect.tac_bind
                                         (Prims.mk_range
                                            "FStar.InteractiveHelpers.PostProcess.fst"
                                            (Prims.of_int (342))
                                            (Prims.of_int (4))
                                            (Prims.of_int (343))
                                            (Prims.of_int (14)))
                                         (Prims.mk_range
                                            "FStar.InteractiveHelpers.PostProcess.fst"
                                            (Prims.of_int (345))
                                            (Prims.of_int (2))
                                            (Prims.of_int (347))
                                            (Prims.of_int (30)))
                                         (if
                                            (FStar_List_Tot_Base.length conjs)
                                              = Prims.int_one
                                          then
                                            Obj.magic
                                              (Obj.repr
                                                 (split_conjunctions_under_match
                                                    dbg t))
                                          else
                                            Obj.magic
                                              (Obj.repr
                                                 (FStar_Tactics_Effect.lift_div_tac
                                                    (fun uu___1 -> conjs))))
                                         (fun uu___ ->
                                            (fun conjs1 ->
                                               Obj.magic
                                                 (FStar_Tactics_Effect.tac_bind
                                                    (Prims.mk_range
                                                       "FStar.InteractiveHelpers.PostProcess.fst"
                                                       (Prims.of_int (345))
                                                       (Prims.of_int (16))
                                                       (Prims.of_int (345))
                                                       (Prims.of_int (38)))
                                                    (Prims.mk_range
                                                       "FStar.InteractiveHelpers.PostProcess.fst"
                                                       (Prims.of_int (347))
                                                       (Prims.of_int (2))
                                                       (Prims.of_int (347))
                                                       (Prims.of_int (30)))
                                                    (FStar_Tactics_Effect.lift_div_tac
                                                       (fun uu___ ->
                                                          FStar_InteractiveHelpers_Propositions.mk_assertions
                                                            conjs1 []))
                                                    (fun uu___ ->
                                                       (fun asserts ->
                                                          Obj.magic
                                                            (FStar_InteractiveHelpers_Output.printout_success
                                                               ge0 asserts))
                                                         uu___))) uu___)))
                                   uu___))) uu___))) uu___)
let (pp_split_assert_conjs :
  Prims.bool -> unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun dbg ->
    fun uu___ ->
      FStar_Tactics_Derived.try_with
        (fun uu___1 ->
           match () with
           | () ->
               FStar_Tactics_Effect.tac_bind
                 (Prims.mk_range "FStar.InteractiveHelpers.PostProcess.fst"
                    (Prims.of_int (353)) (Prims.of_int (14))
                    (Prims.of_int (353)) (Prims.of_int (53)))
                 (Prims.mk_range "FStar.InteractiveHelpers.PostProcess.fst"
                    (Prims.of_int (354)) (Prims.of_int (4))
                    (Prims.of_int (355)) (Prims.of_int (16)))
                 (Obj.magic (find_focused_assert_in_current_goal dbg))
                 (fun uu___2 ->
                    (fun res ->
                       Obj.magic
                         (FStar_Tactics_Effect.tac_bind
                            (Prims.mk_range
                               "FStar.InteractiveHelpers.PostProcess.fst"
                               (Prims.of_int (354)) (Prims.of_int (4))
                               (Prims.of_int (354)) (Prims.of_int (30)))
                            (Prims.mk_range
                               "FStar.InteractiveHelpers.PostProcess.fst"
                               (Prims.of_int (355)) (Prims.of_int (4))
                               (Prims.of_int (355)) (Prims.of_int (16)))
                            (Obj.magic (split_assert_conjs dbg res))
                            (fun uu___2 ->
                               (fun uu___2 -> Obj.magic (end_proof ()))
                                 uu___2))) uu___2))
        (fun uu___1 ->
           match uu___1 with
           | FStar_InteractiveHelpers_Base.MetaAnalysis msg ->
               FStar_Tactics_Effect.tac_bind
                 (Prims.mk_range "FStar.InteractiveHelpers.PostProcess.fst"
                    (Prims.of_int (356)) (Prims.of_int (29))
                    (Prims.of_int (356)) (Prims.of_int (49)))
                 (Prims.mk_range "FStar.InteractiveHelpers.PostProcess.fst"
                    (Prims.of_int (356)) (Prims.of_int (51))
                    (Prims.of_int (356)) (Prims.of_int (63)))
                 (Obj.magic
                    (FStar_InteractiveHelpers_Output.printout_failure msg))
                 (fun uu___2 ->
                    (fun uu___2 -> Obj.magic (end_proof ())) uu___2)
           | err -> FStar_Tactics_Effect.raise err)
let _ =
  FStar_Tactics_Native.register_tactic
    "FStar.InteractiveHelpers.PostProcess.pp_split_assert_conjs"
    (Prims.of_int (3))
    (fun psc ->
       fun ncb ->
         fun args ->
           FStar_Tactics_InterpFuns.mk_tactic_interpretation_2
             (FStar_Tactics_Native.from_tactic_2 pp_split_assert_conjs)
             FStar_Syntax_Embeddings.e_bool FStar_Syntax_Embeddings.e_unit
             FStar_Syntax_Embeddings.e_unit psc ncb args)
type eq_kind =
  | Eq_Dec of FStar_Reflection_Types.typ 
  | Eq_Undec of FStar_Reflection_Types.typ 
  | Eq_Hetero of FStar_Reflection_Types.typ * FStar_Reflection_Types.typ 
let (uu___is_Eq_Dec : eq_kind -> Prims.bool) =
  fun projectee -> match projectee with | Eq_Dec _0 -> true | uu___ -> false
let (__proj__Eq_Dec__item___0 : eq_kind -> FStar_Reflection_Types.typ) =
  fun projectee -> match projectee with | Eq_Dec _0 -> _0
let (uu___is_Eq_Undec : eq_kind -> Prims.bool) =
  fun projectee ->
    match projectee with | Eq_Undec _0 -> true | uu___ -> false
let (__proj__Eq_Undec__item___0 : eq_kind -> FStar_Reflection_Types.typ) =
  fun projectee -> match projectee with | Eq_Undec _0 -> _0
let (uu___is_Eq_Hetero : eq_kind -> Prims.bool) =
  fun projectee ->
    match projectee with | Eq_Hetero (_0, _1) -> true | uu___ -> false
let (__proj__Eq_Hetero__item___0 : eq_kind -> FStar_Reflection_Types.typ) =
  fun projectee -> match projectee with | Eq_Hetero (_0, _1) -> _0
let (__proj__Eq_Hetero__item___1 : eq_kind -> FStar_Reflection_Types.typ) =
  fun projectee -> match projectee with | Eq_Hetero (_0, _1) -> _1
let (is_eq :
  Prims.bool ->
    FStar_Reflection_Types.term ->
      ((eq_kind * FStar_Reflection_Types.term * FStar_Reflection_Types.term)
         FStar_Pervasives_Native.option,
        unit) FStar_Tactics_Effect.tac_repr)
  =
  fun dbg ->
    fun t ->
      FStar_Tactics_Effect.tac_bind
        (Prims.mk_range "FStar.InteractiveHelpers.PostProcess.fst"
           (Prims.of_int (377)) (Prims.of_int (10)) (Prims.of_int (377))
           (Prims.of_int (22)))
        (Prims.mk_range "FStar.InteractiveHelpers.PostProcess.fst"
           (Prims.of_int (378)) (Prims.of_int (2)) (Prims.of_int (397))
           (Prims.of_int (13))) (Obj.magic (remove_b2t t))
        (fun uu___ ->
           (fun t1 ->
              Obj.magic
                (FStar_Tactics_Effect.tac_bind
                   (Prims.mk_range "FStar.InteractiveHelpers.PostProcess.fst"
                      (Prims.of_int (378)) (Prims.of_int (2))
                      (Prims.of_int (378)) (Prims.of_int (49)))
                   (Prims.mk_range "FStar.InteractiveHelpers.PostProcess.fst"
                      (Prims.of_int (379)) (Prims.of_int (2))
                      (Prims.of_int (397)) (Prims.of_int (13)))
                   (Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (Prims.mk_range
                            "FStar.InteractiveHelpers.PostProcess.fst"
                            (Prims.of_int (378)) (Prims.of_int (16))
                            (Prims.of_int (378)) (Prims.of_int (49)))
                         (Prims.mk_range
                            "FStar.InteractiveHelpers.PostProcess.fst"
                            (Prims.of_int (378)) (Prims.of_int (2))
                            (Prims.of_int (378)) (Prims.of_int (49)))
                         (Obj.magic
                            (FStar_Tactics_Effect.tac_bind
                               (Prims.mk_range
                                  "FStar.InteractiveHelpers.PostProcess.fst"
                                  (Prims.of_int (378)) (Prims.of_int (32))
                                  (Prims.of_int (378)) (Prims.of_int (48)))
                               (Prims.mk_range "prims.fst"
                                  (Prims.of_int (606)) (Prims.of_int (19))
                                  (Prims.of_int (606)) (Prims.of_int (31)))
                               (Obj.magic
                                  (FStar_Tactics_Builtins.term_to_string t1))
                               (fun uu___ ->
                                  FStar_Tactics_Effect.lift_div_tac
                                    (fun uu___1 ->
                                       Prims.strcat "[> is_eq: " uu___))))
                         (fun uu___ ->
                            (fun uu___ ->
                               Obj.magic
                                 (FStar_InteractiveHelpers_Base.print_dbg dbg
                                    uu___)) uu___)))
                   (fun uu___ ->
                      (fun uu___ ->
                         Obj.magic
                           (FStar_Tactics_Effect.tac_bind
                              (Prims.mk_range
                                 "FStar.InteractiveHelpers.PostProcess.fst"
                                 (Prims.of_int (379)) (Prims.of_int (19))
                                 (Prims.of_int (379)) (Prims.of_int (32)))
                              (Prims.mk_range
                                 "FStar.InteractiveHelpers.PostProcess.fst"
                                 (Prims.of_int (379)) (Prims.of_int (2))
                                 (Prims.of_int (397)) (Prims.of_int (13)))
                              (FStar_Tactics_Effect.lift_div_tac
                                 (fun uu___1 ->
                                    FStar_Reflection_Derived.collect_app t1))
                              (fun uu___1 ->
                                 (fun uu___1 ->
                                    match uu___1 with
                                    | (hd, params) ->
                                        Obj.magic
                                          (FStar_Tactics_Effect.tac_bind
                                             (Prims.mk_range
                                                "FStar.InteractiveHelpers.PostProcess.fst"
                                                (Prims.of_int (380))
                                                (Prims.of_int (2))
                                                (Prims.of_int (380))
                                                (Prims.of_int (47)))
                                             (Prims.mk_range
                                                "FStar.InteractiveHelpers.PostProcess.fst"
                                                (Prims.of_int (381))
                                                (Prims.of_int (2))
                                                (Prims.of_int (397))
                                                (Prims.of_int (13)))
                                             (Obj.magic
                                                (FStar_Tactics_Effect.tac_bind
                                                   (Prims.mk_range
                                                      "FStar.InteractiveHelpers.PostProcess.fst"
                                                      (Prims.of_int (380))
                                                      (Prims.of_int (16))
                                                      (Prims.of_int (380))
                                                      (Prims.of_int (47)))
                                                   (Prims.mk_range
                                                      "FStar.InteractiveHelpers.PostProcess.fst"
                                                      (Prims.of_int (380))
                                                      (Prims.of_int (2))
                                                      (Prims.of_int (380))
                                                      (Prims.of_int (47)))
                                                   (Obj.magic
                                                      (FStar_Tactics_Effect.tac_bind
                                                         (Prims.mk_range
                                                            "FStar.InteractiveHelpers.PostProcess.fst"
                                                            (Prims.of_int (380))
                                                            (Prims.of_int (29))
                                                            (Prims.of_int (380))
                                                            (Prims.of_int (46)))
                                                         (Prims.mk_range
                                                            "prims.fst"
                                                            (Prims.of_int (606))
                                                            (Prims.of_int (19))
                                                            (Prims.of_int (606))
                                                            (Prims.of_int (31)))
                                                         (Obj.magic
                                                            (FStar_Tactics_Builtins.term_to_string
                                                               hd))
                                                         (fun uu___2 ->
                                                            FStar_Tactics_Effect.lift_div_tac
                                                              (fun uu___3 ->
                                                                 Prims.strcat
                                                                   "- hd:\n"
                                                                   uu___2))))
                                                   (fun uu___2 ->
                                                      (fun uu___2 ->
                                                         Obj.magic
                                                           (FStar_InteractiveHelpers_Base.print_dbg
                                                              dbg uu___2))
                                                        uu___2)))
                                             (fun uu___2 ->
                                                (fun uu___2 ->
                                                   Obj.magic
                                                     (FStar_Tactics_Effect.tac_bind
                                                        (Prims.mk_range
                                                           "FStar.InteractiveHelpers.PostProcess.fst"
                                                           (Prims.of_int (381))
                                                           (Prims.of_int (2))
                                                           (Prims.of_int (381))
                                                           (Prims.of_int (92)))
                                                        (Prims.mk_range
                                                           "FStar.InteractiveHelpers.PostProcess.fst"
                                                           (Prims.of_int (382))
                                                           (Prims.of_int (2))
                                                           (Prims.of_int (397))
                                                           (Prims.of_int (13)))
                                                        (Obj.magic
                                                           (FStar_Tactics_Effect.tac_bind
                                                              (Prims.mk_range
                                                                 "FStar.InteractiveHelpers.PostProcess.fst"
                                                                 (Prims.of_int (381))
                                                                 (Prims.of_int (16))
                                                                 (Prims.of_int (381))
                                                                 (Prims.of_int (92)))
                                                              (Prims.mk_range
                                                                 "FStar.InteractiveHelpers.PostProcess.fst"
                                                                 (Prims.of_int (381))
                                                                 (Prims.of_int (2))
                                                                 (Prims.of_int (381))
                                                                 (Prims.of_int (92)))
                                                              (Obj.magic
                                                                 (FStar_Tactics_Effect.tac_bind
                                                                    (
                                                                    Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (381))
                                                                    (Prims.of_int (37))
                                                                    (Prims.of_int (381))
                                                                    (Prims.of_int (91)))
                                                                    (
                                                                    Prims.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (606))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (606))
                                                                    (Prims.of_int (31)))
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.list_to_string
                                                                    (fun
                                                                    uu___3 ->
                                                                    match uu___3
                                                                    with
                                                                    | 
                                                                    (x, y) ->
                                                                    FStar_Tactics_Builtins.term_to_string
                                                                    x) params))
                                                                    (
                                                                    fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    Prims.strcat
                                                                    "- parameters:\n"
                                                                    uu___3))))
                                                              (fun uu___3 ->
                                                                 (fun uu___3
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    uu___3))
                                                                   uu___3)))
                                                        (fun uu___3 ->
                                                           (fun uu___3 ->
                                                              Obj.magic
                                                                (FStar_Tactics_Effect.tac_bind
                                                                   (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (382))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (382))
                                                                    (Prims.of_int (18)))
                                                                   (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (382))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (397))
                                                                    (Prims.of_int (13)))
                                                                   (Obj.magic
                                                                    (FStar_Tactics_Builtins.inspect
                                                                    hd))
                                                                   (fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    match uu___4
                                                                    with
                                                                    | 
                                                                    FStar_Reflection_Data.Tv_FVar
                                                                    fv ->
                                                                    (match params
                                                                    with
                                                                    | 
                                                                    (a,
                                                                    FStar_Reflection_Data.Q_Implicit)::
                                                                    (x,
                                                                    FStar_Reflection_Data.Q_Explicit)::
                                                                    (y,
                                                                    FStar_Reflection_Data.Q_Explicit)::[]
                                                                    ->
                                                                    if
                                                                    FStar_Reflection_Derived.is_any_fvar
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
                                                                    FStar_Reflection_Derived.is_any_fvar
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
                                                                    FStar_Reflection_Data.Q_Implicit)::
                                                                    (b,
                                                                    FStar_Reflection_Data.Q_Implicit)::
                                                                    (x,
                                                                    FStar_Reflection_Data.Q_Explicit)::
                                                                    (y,
                                                                    FStar_Reflection_Data.Q_Explicit)::[]
                                                                    ->
                                                                    if
                                                                    FStar_Reflection_Derived.is_fvar
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
                                                                    uu___6 ->
                                                                    FStar_Pervasives_Native.None)
                                                                    | 
                                                                    uu___6 ->
                                                                    FStar_Pervasives_Native.None))))
                                                             uu___3))) uu___2)))
                                   uu___1))) uu___))) uu___)
let (mk_eq :
  eq_kind ->
    FStar_Reflection_Types.term ->
      FStar_Reflection_Types.term -> FStar_Reflection_Types.term)
  =
  fun k ->
    fun t1 ->
      fun t2 ->
        match k with
        | Eq_Dec ty ->
            FStar_Reflection_Derived.mk_app
              (FStar_Reflection_Builtins.pack_ln
                 (FStar_Reflection_Data.Tv_FVar
                    (FStar_Reflection_Builtins.pack_fv
                       ["Prims"; "op_Equality"])))
              [(ty, FStar_Reflection_Data.Q_Implicit);
              (t1, FStar_Reflection_Data.Q_Explicit);
              (t2, FStar_Reflection_Data.Q_Explicit)]
        | Eq_Undec ty ->
            FStar_Reflection_Derived.mk_app
              (FStar_Reflection_Builtins.pack_ln
                 (FStar_Reflection_Data.Tv_FVar
                    (FStar_Reflection_Builtins.pack_fv ["Prims"; "eq2"])))
              [(ty, FStar_Reflection_Data.Q_Implicit);
              (t1, FStar_Reflection_Data.Q_Explicit);
              (t2, FStar_Reflection_Data.Q_Explicit)]
        | Eq_Hetero (ty1, ty2) ->
            FStar_Reflection_Derived.mk_app
              (FStar_Reflection_Builtins.pack_ln
                 (FStar_Reflection_Data.Tv_FVar
                    (FStar_Reflection_Builtins.pack_fv
                       ["Prims"; "op_Equals_Equals_Equals"])))
              [(ty1, FStar_Reflection_Data.Q_Implicit);
              (ty2, FStar_Reflection_Data.Q_Implicit);
              (t1, FStar_Reflection_Data.Q_Explicit);
              (t2, FStar_Reflection_Data.Q_Explicit)]
let (formula_construct :
  FStar_Reflection_Formula.formula ->
    (Prims.string, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___ ->
    (fun f ->
       Obj.magic
         (FStar_Tactics_Effect.lift_div_tac
            (fun uu___ ->
               match f with
               | FStar_Reflection_Formula.True_ -> "True_"
               | FStar_Reflection_Formula.False_ -> "False_"
               | FStar_Reflection_Formula.Comp (uu___1, uu___2, uu___3) ->
                   "Comp"
               | FStar_Reflection_Formula.And (uu___1, uu___2) -> "And"
               | FStar_Reflection_Formula.Or (uu___1, uu___2) -> "Or"
               | FStar_Reflection_Formula.Not uu___1 -> "Not"
               | FStar_Reflection_Formula.Implies (uu___1, uu___2) ->
                   "Implies"
               | FStar_Reflection_Formula.Iff (uu___1, uu___2) -> "Iff"
               | FStar_Reflection_Formula.Forall (uu___1, uu___2) -> "Forall"
               | FStar_Reflection_Formula.Exists (uu___1, uu___2) -> "Exists"
               | FStar_Reflection_Formula.App (uu___1, uu___2) -> "Apply"
               | FStar_Reflection_Formula.Name uu___1 -> "Name"
               | FStar_Reflection_Formula.FV uu___1 -> "FV"
               | FStar_Reflection_Formula.IntLit uu___1 -> "IntLit"
               | FStar_Reflection_Formula.F_Unknown -> "F_Unknown"))) uu___
let (is_equality_for_term :
  Prims.bool ->
    FStar_Reflection_Types.term ->
      FStar_Reflection_Types.term ->
        (FStar_Reflection_Types.term FStar_Pervasives_Native.option, 
          unit) FStar_Tactics_Effect.tac_repr)
  =
  fun dbg ->
    fun tm ->
      fun p ->
        FStar_Tactics_Effect.tac_bind
          (Prims.mk_range "FStar.InteractiveHelpers.PostProcess.fst"
             (Prims.of_int (433)) (Prims.of_int (2)) (Prims.of_int (435))
             (Prims.of_int (49)))
          (Prims.mk_range "FStar.InteractiveHelpers.PostProcess.fst"
             (Prims.of_int (438)) (Prims.of_int (2)) (Prims.of_int (459))
             (Prims.of_int (8)))
          (Obj.magic
             (FStar_Tactics_Effect.tac_bind
                (Prims.mk_range "FStar.InteractiveHelpers.PostProcess.fst"
                   (Prims.of_int (433)) (Prims.of_int (16))
                   (Prims.of_int (435)) (Prims.of_int (49)))
                (Prims.mk_range "FStar.InteractiveHelpers.PostProcess.fst"
                   (Prims.of_int (433)) (Prims.of_int (2))
                   (Prims.of_int (435)) (Prims.of_int (49)))
                (Obj.magic
                   (FStar_Tactics_Effect.tac_bind
                      (Prims.mk_range
                         "FStar.InteractiveHelpers.PostProcess.fst"
                         (Prims.of_int (434)) (Prims.of_int (17))
                         (Prims.of_int (435)) (Prims.of_int (48)))
                      (Prims.mk_range "prims.fst" (Prims.of_int (606))
                         (Prims.of_int (19)) (Prims.of_int (606))
                         (Prims.of_int (31)))
                      (Obj.magic
                         (FStar_Tactics_Effect.tac_bind
                            (Prims.mk_range
                               "FStar.InteractiveHelpers.PostProcess.fst"
                               (Prims.of_int (434)) (Prims.of_int (32))
                               (Prims.of_int (435)) (Prims.of_int (48)))
                            (Prims.mk_range "prims.fst" (Prims.of_int (606))
                               (Prims.of_int (19)) (Prims.of_int (606))
                               (Prims.of_int (31)))
                            (Obj.magic
                               (FStar_Tactics_Effect.tac_bind
                                  (Prims.mk_range
                                     "FStar.InteractiveHelpers.PostProcess.fst"
                                     (Prims.of_int (434)) (Prims.of_int (32))
                                     (Prims.of_int (434)) (Prims.of_int (49)))
                                  (Prims.mk_range
                                     "FStar.InteractiveHelpers.PostProcess.fst"
                                     (Prims.of_int (434)) (Prims.of_int (32))
                                     (Prims.of_int (435)) (Prims.of_int (48)))
                                  (Obj.magic
                                     (FStar_Tactics_Builtins.term_to_string
                                        tm))
                                  (fun uu___ ->
                                     (fun uu___ ->
                                        Obj.magic
                                          (FStar_Tactics_Effect.tac_bind
                                             (Prims.mk_range
                                                "FStar.InteractiveHelpers.PostProcess.fst"
                                                (Prims.of_int (435))
                                                (Prims.of_int (17))
                                                (Prims.of_int (435))
                                                (Prims.of_int (48)))
                                             (Prims.mk_range "prims.fst"
                                                (Prims.of_int (606))
                                                (Prims.of_int (19))
                                                (Prims.of_int (606))
                                                (Prims.of_int (31)))
                                             (Obj.magic
                                                (FStar_Tactics_Effect.tac_bind
                                                   (Prims.mk_range
                                                      "FStar.InteractiveHelpers.PostProcess.fst"
                                                      (Prims.of_int (435))
                                                      (Prims.of_int (32))
                                                      (Prims.of_int (435))
                                                      (Prims.of_int (48)))
                                                   (Prims.mk_range
                                                      "prims.fst"
                                                      (Prims.of_int (606))
                                                      (Prims.of_int (19))
                                                      (Prims.of_int (606))
                                                      (Prims.of_int (31)))
                                                   (Obj.magic
                                                      (FStar_Tactics_Builtins.term_to_string
                                                         p))
                                                   (fun uu___1 ->
                                                      FStar_Tactics_Effect.lift_div_tac
                                                        (fun uu___2 ->
                                                           Prims.strcat
                                                             "\n- prop: "
                                                             uu___1))))
                                             (fun uu___1 ->
                                                FStar_Tactics_Effect.lift_div_tac
                                                  (fun uu___2 ->
                                                     Prims.strcat uu___
                                                       uu___1)))) uu___)))
                            (fun uu___ ->
                               FStar_Tactics_Effect.lift_div_tac
                                 (fun uu___1 ->
                                    Prims.strcat "\n- term: " uu___))))
                      (fun uu___ ->
                         FStar_Tactics_Effect.lift_div_tac
                           (fun uu___1 ->
                              Prims.strcat "[> is_equality_for_term:" uu___))))
                (fun uu___ ->
                   (fun uu___ ->
                      Obj.magic
                        (FStar_InteractiveHelpers_Base.print_dbg dbg uu___))
                     uu___)))
          (fun uu___ ->
             (fun uu___ ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (Prims.mk_range
                        "FStar.InteractiveHelpers.PostProcess.fst"
                        (Prims.of_int (439)) (Prims.of_int (4))
                        (Prims.of_int (442)) (Prims.of_int (38)))
                     (Prims.mk_range
                        "FStar.InteractiveHelpers.PostProcess.fst"
                        (Prims.of_int (444)) (Prims.of_int (2))
                        (Prims.of_int (459)) (Prims.of_int (8)))
                     (Obj.magic
                        (FStar_Tactics_Effect.tac_bind
                           (Prims.mk_range
                              "FStar.InteractiveHelpers.PostProcess.fst"
                              (Prims.of_int (439)) (Prims.of_int (10))
                              (Prims.of_int (439)) (Prims.of_int (20)))
                           (Prims.mk_range
                              "FStar.InteractiveHelpers.PostProcess.fst"
                              (Prims.of_int (439)) (Prims.of_int (4))
                              (Prims.of_int (442)) (Prims.of_int (38)))
                           (Obj.magic (FStar_Tactics_Builtins.inspect tm))
                           (fun uu___1 ->
                              FStar_Tactics_Effect.lift_div_tac
                                (fun uu___2 ->
                                   match uu___1 with
                                   | FStar_Reflection_Data.Tv_Var bv ->
                                       (fun tm' ->
                                          FStar_Tactics_Effect.tac_bind
                                            (Prims.mk_range
                                               "FStar.InteractiveHelpers.PostProcess.fst"
                                               (Prims.of_int (441))
                                               (Prims.of_int (24))
                                               (Prims.of_int (441))
                                               (Prims.of_int (35)))
                                            (Prims.mk_range
                                               "FStar.InteractiveHelpers.PostProcess.fst"
                                               (Prims.of_int (441))
                                               (Prims.of_int (18))
                                               (Prims.of_int (441))
                                               (Prims.of_int (82)))
                                            (Obj.magic
                                               (FStar_Tactics_Builtins.inspect
                                                  tm'))
                                            (fun uu___3 ->
                                               FStar_Tactics_Effect.lift_div_tac
                                                 (fun uu___4 ->
                                                    match uu___3 with
                                                    | FStar_Reflection_Data.Tv_Var
                                                        bv' ->
                                                        FStar_InteractiveHelpers_Base.bv_eq
                                                          bv bv'
                                                    | uu___5 -> false)))
                                   | uu___3 -> (fun tm' -> term_eq tm tm')))))
                     (fun uu___1 ->
                        (fun check_eq ->
                           Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (Prims.mk_range
                                   "FStar.InteractiveHelpers.PostProcess.fst"
                                   (Prims.of_int (444)) (Prims.of_int (8))
                                   (Prims.of_int (444)) (Prims.of_int (19)))
                                (Prims.mk_range
                                   "FStar.InteractiveHelpers.PostProcess.fst"
                                   (Prims.of_int (444)) (Prims.of_int (2))
                                   (Prims.of_int (459)) (Prims.of_int (8)))
                                (Obj.magic (is_eq dbg p))
                                (fun uu___1 ->
                                   (fun uu___1 ->
                                      match uu___1 with
                                      | FStar_Pervasives_Native.Some
                                          (ekind, l, r) ->
                                          Obj.magic
                                            (FStar_Tactics_Effect.tac_bind
                                               (Prims.mk_range
                                                  "FStar.InteractiveHelpers.PostProcess.fst"
                                                  (Prims.of_int (448))
                                                  (Prims.of_int (4))
                                                  (Prims.of_int (448))
                                                  (Prims.of_int (80)))
                                               (Prims.mk_range
                                                  "FStar.InteractiveHelpers.PostProcess.fst"
                                                  (Prims.of_int (449))
                                                  (Prims.of_int (4))
                                                  (Prims.of_int (456))
                                                  (Prims.of_int (13)))
                                               (Obj.magic
                                                  (FStar_Tactics_Effect.tac_bind
                                                     (Prims.mk_range
                                                        "FStar.InteractiveHelpers.PostProcess.fst"
                                                        (Prims.of_int (448))
                                                        (Prims.of_int (18))
                                                        (Prims.of_int (448))
                                                        (Prims.of_int (80)))
                                                     (Prims.mk_range
                                                        "FStar.InteractiveHelpers.PostProcess.fst"
                                                        (Prims.of_int (448))
                                                        (Prims.of_int (4))
                                                        (Prims.of_int (448))
                                                        (Prims.of_int (80)))
                                                     (Obj.magic
                                                        (FStar_Tactics_Effect.tac_bind
                                                           (Prims.mk_range
                                                              "FStar.InteractiveHelpers.PostProcess.fst"
                                                              (Prims.of_int (448))
                                                              (Prims.of_int (36))
                                                              (Prims.of_int (448))
                                                              (Prims.of_int (79)))
                                                           (Prims.mk_range
                                                              "prims.fst"
                                                              (Prims.of_int (606))
                                                              (Prims.of_int (19))
                                                              (Prims.of_int (606))
                                                              (Prims.of_int (31)))
                                                           (Obj.magic
                                                              (FStar_Tactics_Effect.tac_bind
                                                                 (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (448))
                                                                    (Prims.of_int (36))
                                                                    (Prims.of_int (448))
                                                                    (Prims.of_int (52)))
                                                                 (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (448))
                                                                    (Prims.of_int (36))
                                                                    (Prims.of_int (448))
                                                                    (Prims.of_int (79)))
                                                                 (Obj.magic
                                                                    (
                                                                    FStar_Tactics_Builtins.term_to_string
                                                                    l))
                                                                 (fun uu___2
                                                                    ->
                                                                    (fun
                                                                    uu___2 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (448))
                                                                    (Prims.of_int (55))
                                                                    (Prims.of_int (448))
                                                                    (Prims.of_int (79)))
                                                                    (Prims.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (606))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (606))
                                                                    (Prims.of_int (31)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (448))
                                                                    (Prims.of_int (63))
                                                                    (Prims.of_int (448))
                                                                    (Prims.of_int (79)))
                                                                    (Prims.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (606))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (606))
                                                                    (Prims.of_int (31)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Builtins.term_to_string
                                                                    r))
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    Prims.strcat
                                                                    " = "
                                                                    uu___3))))
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    Prims.strcat
                                                                    uu___2
                                                                    uu___3))))
                                                                    uu___2)))
                                                           (fun uu___2 ->
                                                              FStar_Tactics_Effect.lift_div_tac
                                                                (fun uu___3
                                                                   ->
                                                                   Prims.strcat
                                                                    "Term is eq: "
                                                                    uu___2))))
                                                     (fun uu___2 ->
                                                        (fun uu___2 ->
                                                           Obj.magic
                                                             (FStar_InteractiveHelpers_Base.print_dbg
                                                                dbg uu___2))
                                                          uu___2)))
                                               (fun uu___2 ->
                                                  (fun uu___2 ->
                                                     if
                                                       uu___is_Eq_Hetero
                                                         ekind
                                                     then
                                                       Obj.magic
                                                         (FStar_Tactics_Effect.tac_bind
                                                            (Prims.mk_range
                                                               "FStar.InteractiveHelpers.PostProcess.fst"
                                                               (Prims.of_int (451))
                                                               (Prims.of_int (6))
                                                               (Prims.of_int (451))
                                                               (Prims.of_int (53)))
                                                            (Prims.mk_range
                                                               "FStar.InteractiveHelpers.PostProcess.fst"
                                                               (Prims.of_int (452))
                                                               (Prims.of_int (6))
                                                               (Prims.of_int (452))
                                                               (Prims.of_int (10)))
                                                            (Obj.magic
                                                               (FStar_InteractiveHelpers_Base.print_dbg
                                                                  dbg
                                                                  "Ignoring heterogeneous equality"))
                                                            (fun uu___3 ->
                                                               FStar_Tactics_Effect.lift_div_tac
                                                                 (fun uu___4
                                                                    ->
                                                                    FStar_Pervasives_Native.None)))
                                                     else
                                                       Obj.magic
                                                         (FStar_Tactics_Effect.tac_bind
                                                            (Prims.mk_range
                                                               "FStar.InteractiveHelpers.PostProcess.fst"
                                                               (Prims.of_int (454))
                                                               (Prims.of_int (12))
                                                               (Prims.of_int (454))
                                                               (Prims.of_int (22)))
                                                            (Prims.mk_range
                                                               "FStar.InteractiveHelpers.PostProcess.fst"
                                                               (Prims.of_int (454))
                                                               (Prims.of_int (9))
                                                               (Prims.of_int (456))
                                                               (Prims.of_int (13)))
                                                            (Obj.magic
                                                               (check_eq l))
                                                            (fun uu___4 ->
                                                               (fun uu___4 ->
                                                                  if uu___4
                                                                  then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Pervasives_Native.Some
                                                                    r)))
                                                                  else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (455))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (455))
                                                                    (Prims.of_int (22)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (455))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (456))
                                                                    (Prims.of_int (13)))
                                                                    (Obj.magic
                                                                    (check_eq
                                                                    r))
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    if uu___6
                                                                    then
                                                                    FStar_Pervasives_Native.Some
                                                                    l
                                                                    else
                                                                    FStar_Pervasives_Native.None)))))
                                                                 uu___4)))
                                                    uu___2))
                                      | uu___2 ->
                                          Obj.magic
                                            (FStar_Tactics_Effect.tac_bind
                                               (Prims.mk_range
                                                  "FStar.InteractiveHelpers.PostProcess.fst"
                                                  (Prims.of_int (458))
                                                  (Prims.of_int (4))
                                                  (Prims.of_int (458))
                                                  (Prims.of_int (34)))
                                               (Prims.mk_range
                                                  "FStar.InteractiveHelpers.PostProcess.fst"
                                                  (Prims.of_int (459))
                                                  (Prims.of_int (4))
                                                  (Prims.of_int (459))
                                                  (Prims.of_int (8)))
                                               (Obj.magic
                                                  (FStar_InteractiveHelpers_Base.print_dbg
                                                     dbg "Term is not eq"))
                                               (fun uu___3 ->
                                                  FStar_Tactics_Effect.lift_div_tac
                                                    (fun uu___4 ->
                                                       FStar_Pervasives_Native.None))))
                                     uu___1))) uu___1))) uu___)
let (find_subequality :
  Prims.bool ->
    FStar_Reflection_Types.term ->
      FStar_Reflection_Types.term ->
        (FStar_Reflection_Types.term FStar_Pervasives_Native.option, 
          unit) FStar_Tactics_Effect.tac_repr)
  =
  fun dbg ->
    fun tm ->
      fun p ->
        FStar_Tactics_Effect.tac_bind
          (Prims.mk_range "FStar.InteractiveHelpers.PostProcess.fst"
             (Prims.of_int (463)) (Prims.of_int (2)) (Prims.of_int (465))
             (Prims.of_int (50)))
          (Prims.mk_range "FStar.InteractiveHelpers.PostProcess.fst"
             (Prims.of_int (466)) (Prims.of_int (2)) (Prims.of_int (468))
             (Prims.of_int (49)))
          (Obj.magic
             (FStar_Tactics_Effect.tac_bind
                (Prims.mk_range "FStar.InteractiveHelpers.PostProcess.fst"
                   (Prims.of_int (463)) (Prims.of_int (16))
                   (Prims.of_int (465)) (Prims.of_int (50)))
                (Prims.mk_range "FStar.InteractiveHelpers.PostProcess.fst"
                   (Prims.of_int (463)) (Prims.of_int (2))
                   (Prims.of_int (465)) (Prims.of_int (50)))
                (Obj.magic
                   (FStar_Tactics_Effect.tac_bind
                      (Prims.mk_range
                         "FStar.InteractiveHelpers.PostProcess.fst"
                         (Prims.of_int (464)) (Prims.of_int (17))
                         (Prims.of_int (465)) (Prims.of_int (49)))
                      (Prims.mk_range "prims.fst" (Prims.of_int (606))
                         (Prims.of_int (19)) (Prims.of_int (606))
                         (Prims.of_int (31)))
                      (Obj.magic
                         (FStar_Tactics_Effect.tac_bind
                            (Prims.mk_range
                               "FStar.InteractiveHelpers.PostProcess.fst"
                               (Prims.of_int (464)) (Prims.of_int (33))
                               (Prims.of_int (465)) (Prims.of_int (49)))
                            (Prims.mk_range "prims.fst" (Prims.of_int (606))
                               (Prims.of_int (19)) (Prims.of_int (606))
                               (Prims.of_int (31)))
                            (Obj.magic
                               (FStar_Tactics_Effect.tac_bind
                                  (Prims.mk_range
                                     "FStar.InteractiveHelpers.PostProcess.fst"
                                     (Prims.of_int (464)) (Prims.of_int (33))
                                     (Prims.of_int (464)) (Prims.of_int (50)))
                                  (Prims.mk_range
                                     "FStar.InteractiveHelpers.PostProcess.fst"
                                     (Prims.of_int (464)) (Prims.of_int (33))
                                     (Prims.of_int (465)) (Prims.of_int (49)))
                                  (Obj.magic
                                     (FStar_Tactics_Builtins.term_to_string
                                        tm))
                                  (fun uu___ ->
                                     (fun uu___ ->
                                        Obj.magic
                                          (FStar_Tactics_Effect.tac_bind
                                             (Prims.mk_range
                                                "FStar.InteractiveHelpers.PostProcess.fst"
                                                (Prims.of_int (465))
                                                (Prims.of_int (17))
                                                (Prims.of_int (465))
                                                (Prims.of_int (49)))
                                             (Prims.mk_range "prims.fst"
                                                (Prims.of_int (606))
                                                (Prims.of_int (19))
                                                (Prims.of_int (606))
                                                (Prims.of_int (31)))
                                             (Obj.magic
                                                (FStar_Tactics_Effect.tac_bind
                                                   (Prims.mk_range
                                                      "FStar.InteractiveHelpers.PostProcess.fst"
                                                      (Prims.of_int (465))
                                                      (Prims.of_int (33))
                                                      (Prims.of_int (465))
                                                      (Prims.of_int (49)))
                                                   (Prims.mk_range
                                                      "prims.fst"
                                                      (Prims.of_int (606))
                                                      (Prims.of_int (19))
                                                      (Prims.of_int (606))
                                                      (Prims.of_int (31)))
                                                   (Obj.magic
                                                      (FStar_Tactics_Builtins.term_to_string
                                                         p))
                                                   (fun uu___1 ->
                                                      FStar_Tactics_Effect.lift_div_tac
                                                        (fun uu___2 ->
                                                           Prims.strcat
                                                             "\n- props: "
                                                             uu___1))))
                                             (fun uu___1 ->
                                                FStar_Tactics_Effect.lift_div_tac
                                                  (fun uu___2 ->
                                                     Prims.strcat uu___
                                                       uu___1)))) uu___)))
                            (fun uu___ ->
                               FStar_Tactics_Effect.lift_div_tac
                                 (fun uu___1 ->
                                    Prims.strcat "\n- ter  : " uu___))))
                      (fun uu___ ->
                         FStar_Tactics_Effect.lift_div_tac
                           (fun uu___1 ->
                              Prims.strcat "[> find_subequality:" uu___))))
                (fun uu___ ->
                   (fun uu___ ->
                      Obj.magic
                        (FStar_InteractiveHelpers_Base.print_dbg dbg uu___))
                     uu___)))
          (fun uu___ ->
             (fun uu___ ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (Prims.mk_range
                        "FStar.InteractiveHelpers.PostProcess.fst"
                        (Prims.of_int (466)) (Prims.of_int (18))
                        (Prims.of_int (466)) (Prims.of_int (38)))
                     (Prims.mk_range
                        "FStar.InteractiveHelpers.PostProcess.fst"
                        (Prims.of_int (467)) (Prims.of_int (2))
                        (Prims.of_int (468)) (Prims.of_int (49)))
                     (Obj.magic (split_conjunctions p))
                     (fun uu___1 ->
                        (fun conjuncts ->
                           Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (Prims.mk_range
                                   "FStar.InteractiveHelpers.PostProcess.fst"
                                   (Prims.of_int (467)) (Prims.of_int (2))
                                   (Prims.of_int (467)) (Prims.of_int (74)))
                                (Prims.mk_range
                                   "FStar.InteractiveHelpers.PostProcess.fst"
                                   (Prims.of_int (468)) (Prims.of_int (2))
                                   (Prims.of_int (468)) (Prims.of_int (49)))
                                (Obj.magic
                                   (FStar_Tactics_Effect.tac_bind
                                      (Prims.mk_range
                                         "FStar.InteractiveHelpers.PostProcess.fst"
                                         (Prims.of_int (467))
                                         (Prims.of_int (16))
                                         (Prims.of_int (467))
                                         (Prims.of_int (74)))
                                      (Prims.mk_range
                                         "FStar.InteractiveHelpers.PostProcess.fst"
                                         (Prims.of_int (467))
                                         (Prims.of_int (2))
                                         (Prims.of_int (467))
                                         (Prims.of_int (74)))
                                      (Obj.magic
                                         (FStar_Tactics_Effect.tac_bind
                                            (Prims.mk_range
                                               "FStar.InteractiveHelpers.PostProcess.fst"
                                               (Prims.of_int (467))
                                               (Prims.of_int (34))
                                               (Prims.of_int (467))
                                               (Prims.of_int (73)))
                                            (Prims.mk_range "prims.fst"
                                               (Prims.of_int (606))
                                               (Prims.of_int (19))
                                               (Prims.of_int (606))
                                               (Prims.of_int (31)))
                                            (Obj.magic
                                               (FStar_InteractiveHelpers_Base.list_to_string
                                                  FStar_Tactics_Builtins.term_to_string
                                                  conjuncts))
                                            (fun uu___1 ->
                                               FStar_Tactics_Effect.lift_div_tac
                                                 (fun uu___2 ->
                                                    Prims.strcat
                                                      "Conjuncts:\n" uu___1))))
                                      (fun uu___1 ->
                                         (fun uu___1 ->
                                            Obj.magic
                                              (FStar_InteractiveHelpers_Base.print_dbg
                                                 dbg uu___1)) uu___1)))
                                (fun uu___1 ->
                                   (fun uu___1 ->
                                      Obj.magic
                                        (FStar_Tactics_Util.tryPick
                                           (is_equality_for_term dbg tm)
                                           conjuncts)) uu___1))) uu___1)))
               uu___)
let (find_equality_from_post :
  Prims.bool ->
    FStar_InteractiveHelpers_Base.genv ->
      FStar_Reflection_Types.term ->
        FStar_Reflection_Types.bv ->
          FStar_Reflection_Types.term ->
            FStar_Reflection_Types.typ ->
              FStar_InteractiveHelpers_Effectful.effect_info ->
                FStar_Reflection_Data.term_view Prims.list ->
                  FStar_Reflection_Data.term_view Prims.list ->
                    ((FStar_InteractiveHelpers_Base.genv *
                       FStar_Reflection_Types.term
                       FStar_Pervasives_Native.option),
                      unit) FStar_Tactics_Effect.tac_repr)
  =
  fun dbg ->
    fun ge0 ->
      fun tm ->
        fun let_bv ->
          fun ret_value ->
            fun ret_type ->
              fun einfo ->
                fun parents ->
                  fun children ->
                    FStar_Tactics_Effect.tac_bind
                      (Prims.mk_range
                         "FStar.InteractiveHelpers.PostProcess.fst"
                         (Prims.of_int (475)) (Prims.of_int (2))
                         (Prims.of_int (475)) (Prims.of_int (44)))
                      (Prims.mk_range
                         "FStar.InteractiveHelpers.PostProcess.fst"
                         (Prims.of_int (476)) (Prims.of_int (2))
                         (Prims.of_int (493)) (Prims.of_int (27)))
                      (Obj.magic
                         (FStar_InteractiveHelpers_Base.print_dbg dbg
                            "[> find_equality_from_post"))
                      (fun uu___ ->
                         (fun uu___ ->
                            Obj.magic
                              (FStar_Tactics_Effect.tac_bind
                                 (Prims.mk_range
                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                    (Prims.of_int (476)) (Prims.of_int (14))
                                    (Prims.of_int (476)) (Prims.of_int (46)))
                                 (Prims.mk_range
                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                    (Prims.of_int (478)) (Prims.of_int (2))
                                    (Prims.of_int (493)) (Prims.of_int (27)))
                                 (Obj.magic
                                    (FStar_InteractiveHelpers_ExploreTerm.get_type_info_from_type
                                       ret_type))
                                 (fun uu___1 ->
                                    (fun tinfo ->
                                       Obj.magic
                                         (FStar_Tactics_Effect.tac_bind
                                            (Prims.mk_range
                                               "FStar.InteractiveHelpers.PostProcess.fst"
                                               (Prims.of_int (479))
                                               (Prims.of_int (4))
                                               (Prims.of_int (480))
                                               (Prims.of_int (78)))
                                            (Prims.mk_range
                                               "FStar.InteractiveHelpers.PostProcess.fst"
                                               (Prims.of_int (478))
                                               (Prims.of_int (2))
                                               (Prims.of_int (493))
                                               (Prims.of_int (27)))
                                            (Obj.magic
                                               (FStar_InteractiveHelpers_Effectful.pre_post_to_propositions
                                                  dbg ge0
                                                  einfo.FStar_InteractiveHelpers_Effectful.ei_type
                                                  ret_value
                                                  (FStar_Pervasives_Native.Some
                                                     (FStar_Reflection_Derived.mk_binder
                                                        let_bv)) tinfo
                                                  einfo.FStar_InteractiveHelpers_Effectful.ei_pre
                                                  einfo.FStar_InteractiveHelpers_Effectful.ei_post
                                                  parents children))
                                            (fun uu___1 ->
                                               (fun uu___1 ->
                                                  match uu___1 with
                                                  | (ge1, uu___2, post_prop)
                                                      ->
                                                      Obj.magic
                                                        (FStar_Tactics_Effect.tac_bind
                                                           (Prims.mk_range
                                                              "FStar.InteractiveHelpers.PostProcess.fst"
                                                              (Prims.of_int (482))
                                                              (Prims.of_int (2))
                                                              (Prims.of_int (482))
                                                              (Prims.of_int (79)))
                                                           (Prims.mk_range
                                                              "FStar.InteractiveHelpers.PostProcess.fst"
                                                              (Prims.of_int (484))
                                                              (Prims.of_int (2))
                                                              (Prims.of_int (493))
                                                              (Prims.of_int (27)))
                                                           (Obj.magic
                                                              (FStar_Tactics_Effect.tac_bind
                                                                 (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (482))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (482))
                                                                    (Prims.of_int (79)))
                                                                 (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (482))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (482))
                                                                    (Prims.of_int (79)))
                                                                 (Obj.magic
                                                                    (
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (482))
                                                                    (Prims.of_int (37))
                                                                    (Prims.of_int (482))
                                                                    (Prims.of_int (78)))
                                                                    (Prims.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (606))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (606))
                                                                    (Prims.of_int (31)))
                                                                    (Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.option_to_string
                                                                    FStar_Tactics_Builtins.term_to_string
                                                                    post_prop))
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    Prims.strcat
                                                                    "Computed post: "
                                                                    uu___3))))
                                                                 (fun uu___3
                                                                    ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    uu___3))
                                                                    uu___3)))
                                                           (fun uu___3 ->
                                                              (fun uu___3 ->
                                                                 Obj.magic
                                                                   (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (485))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (487))
                                                                    (Prims.of_int (41)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (491))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (493))
                                                                    (Prims.of_int (27)))
                                                                    (match post_prop
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Pervasives_Native.None)))
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    p ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (find_subequality
                                                                    dbg tm p)))
                                                                    (fun res
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
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
                                                                uu___3)))
                                                 uu___1))) uu___1))) uu___)
let rec (find_context_equality_aux :
  Prims.bool ->
    FStar_InteractiveHelpers_Base.genv ->
      FStar_Reflection_Types.term ->
        FStar_Reflection_Types.bv FStar_Pervasives_Native.option ->
          FStar_Reflection_Data.term_view Prims.list ->
            FStar_Reflection_Data.term_view Prims.list ->
              ((FStar_InteractiveHelpers_Base.genv *
                 FStar_Reflection_Types.term FStar_Pervasives_Native.option),
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
                                    (FStar_Tactics_Effect.tac_bind
                                       (Prims.mk_range
                                          "FStar.InteractiveHelpers.PostProcess.fst"
                                          (Prims.of_int (512))
                                          (Prims.of_int (4))
                                          (Prims.of_int (514))
                                          (Prims.of_int (52)))
                                       (Prims.mk_range
                                          "FStar.InteractiveHelpers.PostProcess.fst"
                                          (Prims.of_int (516))
                                          (Prims.of_int (4))
                                          (Prims.of_int (540))
                                          (Prims.of_int (79)))
                                       (Obj.magic
                                          (FStar_Tactics_Effect.tac_bind
                                             (Prims.mk_range
                                                "FStar.InteractiveHelpers.PostProcess.fst"
                                                (Prims.of_int (512))
                                                (Prims.of_int (18))
                                                (Prims.of_int (514))
                                                (Prims.of_int (52)))
                                             (Prims.mk_range
                                                "FStar.InteractiveHelpers.PostProcess.fst"
                                                (Prims.of_int (512))
                                                (Prims.of_int (4))
                                                (Prims.of_int (514))
                                                (Prims.of_int (52)))
                                             (Obj.magic
                                                (FStar_Tactics_Effect.tac_bind
                                                   (Prims.mk_range
                                                      "FStar.InteractiveHelpers.PostProcess.fst"
                                                      (Prims.of_int (513))
                                                      (Prims.of_int (19))
                                                      (Prims.of_int (514))
                                                      (Prims.of_int (51)))
                                                   (Prims.mk_range
                                                      "prims.fst"
                                                      (Prims.of_int (606))
                                                      (Prims.of_int (19))
                                                      (Prims.of_int (606))
                                                      (Prims.of_int (31)))
                                                   (Obj.magic
                                                      (FStar_Tactics_Effect.tac_bind
                                                         (Prims.mk_range
                                                            "FStar.InteractiveHelpers.PostProcess.fst"
                                                            (Prims.of_int (513))
                                                            (Prims.of_int (34))
                                                            (Prims.of_int (514))
                                                            (Prims.of_int (51)))
                                                         (Prims.mk_range
                                                            "prims.fst"
                                                            (Prims.of_int (606))
                                                            (Prims.of_int (19))
                                                            (Prims.of_int (606))
                                                            (Prims.of_int (31)))
                                                         (Obj.magic
                                                            (FStar_Tactics_Effect.tac_bind
                                                               (Prims.mk_range
                                                                  "FStar.InteractiveHelpers.PostProcess.fst"
                                                                  (Prims.of_int (513))
                                                                  (Prims.of_int (34))
                                                                  (Prims.of_int (513))
                                                                  (Prims.of_int (51)))
                                                               (Prims.mk_range
                                                                  "FStar.InteractiveHelpers.PostProcess.fst"
                                                                  (Prims.of_int (513))
                                                                  (Prims.of_int (34))
                                                                  (Prims.of_int (514))
                                                                  (Prims.of_int (51)))
                                                               (Obj.magic
                                                                  (FStar_Tactics_Builtins.term_to_string
                                                                    tm))
                                                               (fun uu___ ->
                                                                  (fun uu___
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (513))
                                                                    (Prims.of_int (54))
                                                                    (Prims.of_int (514))
                                                                    (Prims.of_int (51)))
                                                                    (Prims.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (606))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (606))
                                                                    (Prims.of_int (31)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (514))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (514))
                                                                    (Prims.of_int (51)))
                                                                    (Prims.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (606))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (606))
                                                                    (Prims.of_int (31)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (514))
                                                                    (Prims.of_int (34))
                                                                    (Prims.of_int (514))
                                                                    (Prims.of_int (51)))
                                                                    (Prims.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (606))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (606))
                                                                    (Prims.of_int (31)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (511))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (511))
                                                                    (Prims.of_int (6)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (514))
                                                                    (Prims.of_int (34))
                                                                    (Prims.of_int (514))
                                                                    (Prims.of_int (51)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Builtins.pack
                                                                    tv))
                                                                    (fun
                                                                    uu___1 ->
                                                                    (fun
                                                                    uu___1 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Builtins.term_to_string
                                                                    uu___1))
                                                                    uu___1)))
                                                                    (fun
                                                                    uu___1 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    Prims.strcat
                                                                    "- parent: "
                                                                    uu___1))))
                                                                    (fun
                                                                    uu___1 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    Prims.strcat
                                                                    "\n"
                                                                    uu___1))))
                                                                    (fun
                                                                    uu___1 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    Prims.strcat
                                                                    uu___
                                                                    uu___1))))
                                                                    uu___)))
                                                         (fun uu___ ->
                                                            FStar_Tactics_Effect.lift_div_tac
                                                              (fun uu___1 ->
                                                                 Prims.strcat
                                                                   "- term  : "
                                                                   uu___))))
                                                   (fun uu___ ->
                                                      FStar_Tactics_Effect.lift_div_tac
                                                        (fun uu___1 ->
                                                           Prims.strcat
                                                             "[> find_context_equality:\n"
                                                             uu___))))
                                             (fun uu___ ->
                                                (fun uu___ ->
                                                   Obj.magic
                                                     (FStar_InteractiveHelpers_Base.print_dbg
                                                        dbg uu___)) uu___)))
                                       (fun uu___ ->
                                          (fun uu___ ->
                                             match tv with
                                             | FStar_Reflection_Data.Tv_Let
                                                 (uu___1, uu___2, bv', def,
                                                  uu___3)
                                                 ->
                                                 Obj.magic
                                                   (FStar_Tactics_Effect.tac_bind
                                                      (Prims.mk_range
                                                         "FStar.InteractiveHelpers.PostProcess.fst"
                                                         (Prims.of_int (518))
                                                         (Prims.of_int (6))
                                                         (Prims.of_int (518))
                                                         (Prims.of_int (31)))
                                                      (Prims.mk_range
                                                         "FStar.InteractiveHelpers.PostProcess.fst"
                                                         (Prims.of_int (519))
                                                         (Prims.of_int (6))
                                                         (Prims.of_int (539))
                                                         (Prims.of_int (11)))
                                                      (Obj.magic
                                                         (FStar_InteractiveHelpers_Base.print_dbg
                                                            dbg "Is Tv_Let"))
                                                      (fun uu___4 ->
                                                         (fun uu___4 ->
                                                            Obj.magic
                                                              (FStar_Tactics_Effect.tac_bind
                                                                 (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (519))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (519))
                                                                    (Prims.of_int (54)))
                                                                 (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (520))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (539))
                                                                    (Prims.of_int (11)))
                                                                 (Obj.magic
                                                                    (
                                                                    FStar_InteractiveHelpers_Effectful.compute_eterm_info
                                                                    dbg
                                                                    ge0.FStar_InteractiveHelpers_Base.env
                                                                    def))
                                                                 (fun uu___5
                                                                    ->
                                                                    (fun
                                                                    tm_info
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (520))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (520))
                                                                    (Prims.of_int (31)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (526))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (539))
                                                                    (Prims.of_int (11)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    tm_info.FStar_InteractiveHelpers_Effectful.einfo))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    einfo ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (527))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (529))
                                                                    (Prims.of_int (23)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (531))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (539))
                                                                    (Prims.of_int (11)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    match opt_bv
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    tm_bv ->
                                                                    FStar_InteractiveHelpers_Base.bv_eq
                                                                    tm_bv bv'
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    -> false))
                                                                    (fun
                                                                    uu___5 ->
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
                                                                    uu___5 ->
                                                                    (ge0,
                                                                    (FStar_Pervasives_Native.Some
                                                                    def)))))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (533))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (533))
                                                                    (Prims.of_int (41)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (534))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (539))
                                                                    (Prims.of_int (11)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Builtins.pack
                                                                    (FStar_Reflection_Data.Tv_Var
                                                                    bv')))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    ret_value
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (534))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (534))
                                                                    (Prims.of_int (36)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (535))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (538))
                                                                    (Prims.of_int (90)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Reflection_Derived.type_of_bv
                                                                    bv'))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    ret_typ
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (535))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (536))
                                                                    (Prims.of_int (66)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (535))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (538))
                                                                    (Prims.of_int (90)))
                                                                    (Obj.magic
                                                                    (find_equality_from_post
                                                                    dbg ge0
                                                                    tm bv'
                                                                    ret_value
                                                                    ret_typ
                                                                    einfo
                                                                    parents
                                                                    children))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    uu___6 ->
                                                                    match uu___6
                                                                    with
                                                                    | 
                                                                    (ge1,
                                                                    FStar_Pervasives_Native.Some
                                                                    p) ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    (ge1,
                                                                    (FStar_Pervasives_Native.Some
                                                                    p)))))
                                                                    | 
                                                                    (uu___7,
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
                                                                    uu___6)))
                                                                    uu___6)))
                                                                    uu___6))))
                                                                    uu___5)))
                                                                    uu___5)))
                                                                    uu___5)))
                                                           uu___4))
                                             | uu___1 ->
                                                 Obj.magic
                                                   (find_context_equality_aux
                                                      dbg ge0 tm opt_bv
                                                      parents' (tv ::
                                                      children))) uu___))))
                uu___5 uu___4 uu___3 uu___2 uu___1 uu___
let (find_context_equality :
  Prims.bool ->
    FStar_InteractiveHelpers_Base.genv ->
      FStar_Reflection_Types.term ->
        FStar_Reflection_Data.term_view Prims.list ->
          FStar_Reflection_Data.term_view Prims.list ->
            ((FStar_InteractiveHelpers_Base.genv *
               FStar_Reflection_Types.term FStar_Pervasives_Native.option),
              unit) FStar_Tactics_Effect.tac_repr)
  =
  fun dbg ->
    fun ge0 ->
      fun tm ->
        fun parents ->
          fun children ->
            FStar_Tactics_Effect.tac_bind
              (Prims.mk_range "FStar.InteractiveHelpers.PostProcess.fst"
                 (Prims.of_int (544)) (Prims.of_int (4)) (Prims.of_int (546))
                 (Prims.of_int (15)))
              (Prims.mk_range "FStar.InteractiveHelpers.PostProcess.fst"
                 (Prims.of_int (548)) (Prims.of_int (2)) (Prims.of_int (548))
                 (Prims.of_int (62)))
              (Obj.magic
                 (FStar_Tactics_Effect.tac_bind
                    (Prims.mk_range
                       "FStar.InteractiveHelpers.PostProcess.fst"
                       (Prims.of_int (544)) (Prims.of_int (10))
                       (Prims.of_int (544)) (Prims.of_int (20)))
                    (Prims.mk_range
                       "FStar.InteractiveHelpers.PostProcess.fst"
                       (Prims.of_int (544)) (Prims.of_int (4))
                       (Prims.of_int (546)) (Prims.of_int (15)))
                    (Obj.magic (FStar_Tactics_Builtins.inspect tm))
                    (fun uu___ ->
                       FStar_Tactics_Effect.lift_div_tac
                         (fun uu___1 ->
                            match uu___ with
                            | FStar_Reflection_Data.Tv_Var bv ->
                                FStar_Pervasives_Native.Some bv
                            | uu___2 -> FStar_Pervasives_Native.None))))
              (fun uu___ ->
                 (fun opt_bv ->
                    Obj.magic
                      (find_context_equality_aux dbg ge0 tm opt_bv parents
                         children)) uu___)
let rec (replace_term_in :
  Prims.bool ->
    FStar_Reflection_Types.term ->
      FStar_Reflection_Types.term ->
        FStar_Reflection_Types.term ->
          (FStar_Reflection_Types.term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun dbg ->
    fun from_term ->
      fun to_term ->
        fun tm ->
          FStar_Tactics_Effect.tac_bind
            (Prims.mk_range "FStar.InteractiveHelpers.PostProcess.fst"
               (Prims.of_int (553)) (Prims.of_int (5)) (Prims.of_int (553))
               (Prims.of_int (25)))
            (Prims.mk_range "FStar.InteractiveHelpers.PostProcess.fst"
               (Prims.of_int (553)) (Prims.of_int (2)) (Prims.of_int (594))
               (Prims.of_int (6))) (Obj.magic (term_eq from_term tm))
            (fun uu___ ->
               (fun uu___ ->
                  if uu___
                  then
                    Obj.magic
                      (Obj.repr
                         (FStar_Tactics_Effect.lift_div_tac
                            (fun uu___1 -> to_term)))
                  else
                    Obj.magic
                      (Obj.repr
                         (FStar_Tactics_Effect.tac_bind
                            (Prims.mk_range
                               "FStar.InteractiveHelpers.PostProcess.fst"
                               (Prims.of_int (554)) (Prims.of_int (8))
                               (Prims.of_int (554)) (Prims.of_int (18)))
                            (Prims.mk_range
                               "FStar.InteractiveHelpers.PostProcess.fst"
                               (Prims.of_int (554)) (Prims.of_int (2))
                               (Prims.of_int (594)) (Prims.of_int (6)))
                            (Obj.magic (FStar_Tactics_Builtins.inspect tm))
                            (fun uu___2 ->
                               (fun uu___2 ->
                                  match uu___2 with
                                  | FStar_Reflection_Data.Tv_Var uu___3 ->
                                      Obj.magic
                                        (Obj.repr
                                           (FStar_Tactics_Effect.lift_div_tac
                                              (fun uu___4 -> tm)))
                                  | FStar_Reflection_Data.Tv_BVar uu___3 ->
                                      Obj.magic
                                        (Obj.repr
                                           (FStar_Tactics_Effect.lift_div_tac
                                              (fun uu___4 -> tm)))
                                  | FStar_Reflection_Data.Tv_FVar uu___3 ->
                                      Obj.magic
                                        (Obj.repr
                                           (FStar_Tactics_Effect.lift_div_tac
                                              (fun uu___4 -> tm)))
                                  | FStar_Reflection_Data.Tv_App
                                      (hd, (a, qual)) ->
                                      Obj.magic
                                        (Obj.repr
                                           (FStar_Tactics_Effect.tac_bind
                                              (Prims.mk_range
                                                 "FStar.InteractiveHelpers.PostProcess.fst"
                                                 (Prims.of_int (557))
                                                 (Prims.of_int (13))
                                                 (Prims.of_int (557))
                                                 (Prims.of_int (52)))
                                              (Prims.mk_range
                                                 "FStar.InteractiveHelpers.PostProcess.fst"
                                                 (Prims.of_int (558))
                                                 (Prims.of_int (4))
                                                 (Prims.of_int (559))
                                                 (Prims.of_int (32)))
                                              (Obj.magic
                                                 (replace_term_in dbg
                                                    from_term to_term a))
                                              (fun uu___3 ->
                                                 (fun a' ->
                                                    Obj.magic
                                                      (FStar_Tactics_Effect.tac_bind
                                                         (Prims.mk_range
                                                            "FStar.InteractiveHelpers.PostProcess.fst"
                                                            (Prims.of_int (558))
                                                            (Prims.of_int (14))
                                                            (Prims.of_int (558))
                                                            (Prims.of_int (54)))
                                                         (Prims.mk_range
                                                            "FStar.InteractiveHelpers.PostProcess.fst"
                                                            (Prims.of_int (559))
                                                            (Prims.of_int (4))
                                                            (Prims.of_int (559))
                                                            (Prims.of_int (32)))
                                                         (Obj.magic
                                                            (replace_term_in
                                                               dbg from_term
                                                               to_term hd))
                                                         (fun uu___3 ->
                                                            (fun hd' ->
                                                               Obj.magic
                                                                 (FStar_Tactics_Builtins.pack
                                                                    (
                                                                    FStar_Reflection_Data.Tv_App
                                                                    (hd',
                                                                    (a',
                                                                    qual)))))
                                                              uu___3)))
                                                   uu___3)))
                                  | FStar_Reflection_Data.Tv_Abs (br, body)
                                      ->
                                      Obj.magic
                                        (Obj.repr
                                           (FStar_Tactics_Effect.tac_bind
                                              (Prims.mk_range
                                                 "FStar.InteractiveHelpers.PostProcess.fst"
                                                 (Prims.of_int (561))
                                                 (Prims.of_int (16))
                                                 (Prims.of_int (561))
                                                 (Prims.of_int (58)))
                                              (Prims.mk_range
                                                 "FStar.InteractiveHelpers.PostProcess.fst"
                                                 (Prims.of_int (562))
                                                 (Prims.of_int (4))
                                                 (Prims.of_int (562))
                                                 (Prims.of_int (26)))
                                              (Obj.magic
                                                 (replace_term_in dbg
                                                    from_term to_term body))
                                              (fun uu___3 ->
                                                 (fun body' ->
                                                    Obj.magic
                                                      (FStar_Tactics_Builtins.pack
                                                         (FStar_Reflection_Data.Tv_Abs
                                                            (br, body'))))
                                                   uu___3)))
                                  | FStar_Reflection_Data.Tv_Arrow (br, c0)
                                      ->
                                      Obj.magic
                                        (Obj.repr
                                           (FStar_Tactics_Effect.lift_div_tac
                                              (fun uu___3 -> tm)))
                                  | FStar_Reflection_Data.Tv_Type uu___3 ->
                                      Obj.magic
                                        (Obj.repr
                                           (FStar_Tactics_Effect.lift_div_tac
                                              (fun uu___4 -> tm)))
                                  | FStar_Reflection_Data.Tv_Refine (bv, ref)
                                      ->
                                      Obj.magic
                                        (Obj.repr
                                           (FStar_Tactics_Effect.tac_bind
                                              (Prims.mk_range
                                                 "FStar.InteractiveHelpers.PostProcess.fst"
                                                 (Prims.of_int (566))
                                                 (Prims.of_int (15))
                                                 (Prims.of_int (566))
                                                 (Prims.of_int (56)))
                                              (Prims.mk_range
                                                 "FStar.InteractiveHelpers.PostProcess.fst"
                                                 (Prims.of_int (567))
                                                 (Prims.of_int (4))
                                                 (Prims.of_int (567))
                                                 (Prims.of_int (28)))
                                              (Obj.magic
                                                 (replace_term_in dbg
                                                    from_term to_term ref))
                                              (fun uu___3 ->
                                                 (fun ref' ->
                                                    Obj.magic
                                                      (FStar_Tactics_Builtins.pack
                                                         (FStar_Reflection_Data.Tv_Refine
                                                            (bv, ref'))))
                                                   uu___3)))
                                  | FStar_Reflection_Data.Tv_Const uu___3 ->
                                      Obj.magic
                                        (Obj.repr
                                           (FStar_Tactics_Effect.lift_div_tac
                                              (fun uu___4 -> tm)))
                                  | FStar_Reflection_Data.Tv_Uvar
                                      (uu___3, uu___4) ->
                                      Obj.magic
                                        (Obj.repr
                                           (FStar_Tactics_Effect.lift_div_tac
                                              (fun uu___5 -> tm)))
                                  | FStar_Reflection_Data.Tv_Let
                                      (recf, attrs, bv, def, body) ->
                                      Obj.magic
                                        (Obj.repr
                                           (FStar_Tactics_Effect.tac_bind
                                              (Prims.mk_range
                                                 "FStar.InteractiveHelpers.PostProcess.fst"
                                                 (Prims.of_int (571))
                                                 (Prims.of_int (15))
                                                 (Prims.of_int (571))
                                                 (Prims.of_int (56)))
                                              (Prims.mk_range
                                                 "FStar.InteractiveHelpers.PostProcess.fst"
                                                 (Prims.of_int (572))
                                                 (Prims.of_int (4))
                                                 (Prims.of_int (573))
                                                 (Prims.of_int (42)))
                                              (Obj.magic
                                                 (replace_term_in dbg
                                                    from_term to_term def))
                                              (fun uu___3 ->
                                                 (fun def' ->
                                                    Obj.magic
                                                      (FStar_Tactics_Effect.tac_bind
                                                         (Prims.mk_range
                                                            "FStar.InteractiveHelpers.PostProcess.fst"
                                                            (Prims.of_int (572))
                                                            (Prims.of_int (16))
                                                            (Prims.of_int (572))
                                                            (Prims.of_int (58)))
                                                         (Prims.mk_range
                                                            "FStar.InteractiveHelpers.PostProcess.fst"
                                                            (Prims.of_int (573))
                                                            (Prims.of_int (4))
                                                            (Prims.of_int (573))
                                                            (Prims.of_int (42)))
                                                         (Obj.magic
                                                            (replace_term_in
                                                               dbg from_term
                                                               to_term body))
                                                         (fun uu___3 ->
                                                            (fun body' ->
                                                               Obj.magic
                                                                 (FStar_Tactics_Builtins.pack
                                                                    (
                                                                    FStar_Reflection_Data.Tv_Let
                                                                    (recf,
                                                                    attrs,
                                                                    bv, def',
                                                                    body'))))
                                                              uu___3)))
                                                   uu___3)))
                                  | FStar_Reflection_Data.Tv_Match
                                      (scrutinee, ret_opt, branches) ->
                                      Obj.magic
                                        (Obj.repr
                                           (FStar_Tactics_Effect.tac_bind
                                              (Prims.mk_range
                                                 "FStar.InteractiveHelpers.PostProcess.fst"
                                                 (Prims.of_int (578))
                                                 (Prims.of_int (6))
                                                 (Prims.of_int (580))
                                                 (Prims.of_int (18)))
                                              (Prims.mk_range
                                                 "FStar.InteractiveHelpers.PostProcess.fst"
                                                 (Prims.of_int (582))
                                                 (Prims.of_int (4))
                                                 (Prims.of_int (584))
                                                 (Prims.of_int (48)))
                                              (FStar_Tactics_Effect.lift_div_tac
                                                 (fun uu___3 ->
                                                    fun br ->
                                                      FStar_Tactics_Effect.tac_bind
                                                        (Prims.mk_range
                                                           "FStar.InteractiveHelpers.PostProcess.fst"
                                                           (Prims.of_int (578))
                                                           (Prims.of_int (22))
                                                           (Prims.of_int (578))
                                                           (Prims.of_int (24)))
                                                        (Prims.mk_range
                                                           "FStar.InteractiveHelpers.PostProcess.fst"
                                                           (Prims.of_int (578))
                                                           (Prims.of_int (6))
                                                           (Prims.of_int (580))
                                                           (Prims.of_int (18)))
                                                        (FStar_Tactics_Effect.lift_div_tac
                                                           (fun uu___4 -> br))
                                                        (fun uu___4 ->
                                                           (fun uu___4 ->
                                                              match uu___4
                                                              with
                                                              | (pat, body)
                                                                  ->
                                                                  Obj.magic
                                                                    (
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (579))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (579))
                                                                    (Prims.of_int (60)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (580))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (580))
                                                                    (Prims.of_int (18)))
                                                                    (Obj.magic
                                                                    (replace_term_in
                                                                    dbg
                                                                    from_term
                                                                    to_term
                                                                    body))
                                                                    (fun
                                                                    body' ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    (pat,
                                                                    body')))))
                                                             uu___4)))
                                              (fun uu___3 ->
                                                 (fun explore_branch ->
                                                    Obj.magic
                                                      (FStar_Tactics_Effect.tac_bind
                                                         (Prims.mk_range
                                                            "FStar.InteractiveHelpers.PostProcess.fst"
                                                            (Prims.of_int (582))
                                                            (Prims.of_int (21))
                                                            (Prims.of_int (582))
                                                            (Prims.of_int (68)))
                                                         (Prims.mk_range
                                                            "FStar.InteractiveHelpers.PostProcess.fst"
                                                            (Prims.of_int (583))
                                                            (Prims.of_int (4))
                                                            (Prims.of_int (584))
                                                            (Prims.of_int (48)))
                                                         (Obj.magic
                                                            (replace_term_in
                                                               dbg from_term
                                                               to_term
                                                               scrutinee))
                                                         (fun uu___3 ->
                                                            (fun scrutinee'
                                                               ->
                                                               Obj.magic
                                                                 (FStar_Tactics_Effect.tac_bind
                                                                    (
                                                                    Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (583))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (583))
                                                                    (Prims.of_int (47)))
                                                                    (
                                                                    Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (584))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (584))
                                                                    (Prims.of_int (48)))
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Tactics_Util.map
                                                                    explore_branch
                                                                    branches))
                                                                    (
                                                                    fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    branches'
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Builtins.pack
                                                                    (FStar_Reflection_Data.Tv_Match
                                                                    (scrutinee',
                                                                    ret_opt,
                                                                    branches'))))
                                                                    uu___3)))
                                                              uu___3)))
                                                   uu___3)))
                                  | FStar_Reflection_Data.Tv_AscribedT
                                      (e, ty, tac, use_eq) ->
                                      Obj.magic
                                        (Obj.repr
                                           (FStar_Tactics_Effect.tac_bind
                                              (Prims.mk_range
                                                 "FStar.InteractiveHelpers.PostProcess.fst"
                                                 (Prims.of_int (586))
                                                 (Prims.of_int (13))
                                                 (Prims.of_int (586))
                                                 (Prims.of_int (52)))
                                              (Prims.mk_range
                                                 "FStar.InteractiveHelpers.PostProcess.fst"
                                                 (Prims.of_int (587))
                                                 (Prims.of_int (4))
                                                 (Prims.of_int (588))
                                                 (Prims.of_int (41)))
                                              (Obj.magic
                                                 (replace_term_in dbg
                                                    from_term to_term e))
                                              (fun uu___3 ->
                                                 (fun e' ->
                                                    Obj.magic
                                                      (FStar_Tactics_Effect.tac_bind
                                                         (Prims.mk_range
                                                            "FStar.InteractiveHelpers.PostProcess.fst"
                                                            (Prims.of_int (587))
                                                            (Prims.of_int (14))
                                                            (Prims.of_int (587))
                                                            (Prims.of_int (54)))
                                                         (Prims.mk_range
                                                            "FStar.InteractiveHelpers.PostProcess.fst"
                                                            (Prims.of_int (588))
                                                            (Prims.of_int (4))
                                                            (Prims.of_int (588))
                                                            (Prims.of_int (41)))
                                                         (Obj.magic
                                                            (replace_term_in
                                                               dbg from_term
                                                               to_term ty))
                                                         (fun uu___3 ->
                                                            (fun ty' ->
                                                               Obj.magic
                                                                 (FStar_Tactics_Builtins.pack
                                                                    (
                                                                    FStar_Reflection_Data.Tv_AscribedT
                                                                    (e', ty',
                                                                    tac,
                                                                    use_eq))))
                                                              uu___3)))
                                                   uu___3)))
                                  | FStar_Reflection_Data.Tv_AscribedC
                                      (e, c, tac, use_eq) ->
                                      Obj.magic
                                        (Obj.repr
                                           (FStar_Tactics_Effect.tac_bind
                                              (Prims.mk_range
                                                 "FStar.InteractiveHelpers.PostProcess.fst"
                                                 (Prims.of_int (590))
                                                 (Prims.of_int (13))
                                                 (Prims.of_int (590))
                                                 (Prims.of_int (52)))
                                              (Prims.mk_range
                                                 "FStar.InteractiveHelpers.PostProcess.fst"
                                                 (Prims.of_int (591))
                                                 (Prims.of_int (4))
                                                 (Prims.of_int (591))
                                                 (Prims.of_int (39)))
                                              (Obj.magic
                                                 (replace_term_in dbg
                                                    from_term to_term e))
                                              (fun uu___3 ->
                                                 (fun e' ->
                                                    Obj.magic
                                                      (FStar_Tactics_Builtins.pack
                                                         (FStar_Reflection_Data.Tv_AscribedC
                                                            (e', c, tac,
                                                              use_eq))))
                                                   uu___3)))
                                  | uu___3 ->
                                      Obj.magic
                                        (Obj.repr
                                           (FStar_Tactics_Effect.lift_div_tac
                                              (fun uu___4 -> tm)))) uu___2))))
                 uu___)
let rec (strip_implicit_parameters :
  FStar_Reflection_Types.term ->
    (FStar_Reflection_Types.term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun tm ->
    FStar_Tactics_Effect.tac_bind
      (Prims.mk_range "FStar.InteractiveHelpers.PostProcess.fst"
         (Prims.of_int (598)) (Prims.of_int (8)) (Prims.of_int (598))
         (Prims.of_int (18)))
      (Prims.mk_range "FStar.InteractiveHelpers.PostProcess.fst"
         (Prims.of_int (598)) (Prims.of_int (2)) (Prims.of_int (601))
         (Prims.of_int (11))) (Obj.magic (FStar_Tactics_Builtins.inspect tm))
      (fun uu___ ->
         (fun uu___ ->
            match uu___ with
            | FStar_Reflection_Data.Tv_App (hd, (a, qualif)) ->
                Obj.magic
                  (Obj.repr
                     (if FStar_Reflection_Data.uu___is_Q_Implicit qualif
                      then Obj.repr (strip_implicit_parameters hd)
                      else
                        Obj.repr
                          (FStar_Tactics_Effect.lift_div_tac
                             (fun uu___2 -> tm))))
            | uu___1 ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.lift_div_tac (fun uu___2 -> tm))))
           uu___)
let (unfold_in_assert_or_assume :
  Prims.bool ->
    FStar_Reflection_Types.term exploration_result ->
      (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun dbg ->
    fun ares ->
      FStar_Tactics_Effect.tac_bind
        (Prims.mk_range "FStar.InteractiveHelpers.PostProcess.fst"
           (Prims.of_int (605)) (Prims.of_int (2)) (Prims.of_int (605))
           (Prims.of_int (78)))
        (Prims.mk_range "FStar.InteractiveHelpers.PostProcess.fst"
           (Prims.of_int (608)) (Prims.of_int (2)) (Prims.of_int (739))
           (Prims.of_int (30)))
        (Obj.magic
           (FStar_Tactics_Effect.tac_bind
              (Prims.mk_range "FStar.InteractiveHelpers.PostProcess.fst"
                 (Prims.of_int (605)) (Prims.of_int (16))
                 (Prims.of_int (605)) (Prims.of_int (78)))
              (Prims.mk_range "FStar.InteractiveHelpers.PostProcess.fst"
                 (Prims.of_int (605)) (Prims.of_int (2)) (Prims.of_int (605))
                 (Prims.of_int (78)))
              (Obj.magic
                 (FStar_Tactics_Effect.tac_bind
                    (Prims.mk_range
                       "FStar.InteractiveHelpers.PostProcess.fst"
                       (Prims.of_int (605)) (Prims.of_int (54))
                       (Prims.of_int (605)) (Prims.of_int (77)))
                    (Prims.mk_range "prims.fst" (Prims.of_int (606))
                       (Prims.of_int (19)) (Prims.of_int (606))
                       (Prims.of_int (31)))
                    (Obj.magic
                       (FStar_Tactics_Builtins.term_to_string ares.res))
                    (fun uu___ ->
                       FStar_Tactics_Effect.lift_div_tac
                         (fun uu___1 ->
                            Prims.strcat "[> unfold_in_assert_or_assume:\n"
                              uu___))))
              (fun uu___ ->
                 (fun uu___ ->
                    Obj.magic
                      (FStar_InteractiveHelpers_Base.print_dbg dbg uu___))
                   uu___)))
        (fun uu___ ->
           (fun uu___ ->
              Obj.magic
                (FStar_Tactics_Effect.tac_bind
                   (Prims.mk_range "FStar.InteractiveHelpers.PostProcess.fst"
                      (Prims.of_int (609)) (Prims.of_int (4))
                      (Prims.of_int (609)) (Prims.of_int (68)))
                   (Prims.mk_range "FStar.InteractiveHelpers.PostProcess.fst"
                      (Prims.of_int (611)) (Prims.of_int (2))
                      (Prims.of_int (739)) (Prims.of_int (30)))
                   (FStar_Tactics_Effect.lift_div_tac
                      (fun uu___1 ->
                         fun t ->
                           find_focused_term dbg false ares.ge ares.parents
                             ares.tgt_comp t))
                   (fun uu___1 ->
                      (fun find_focused_in_term ->
                         Obj.magic
                           (FStar_Tactics_Effect.tac_bind
                              (Prims.mk_range
                                 "FStar.InteractiveHelpers.PostProcess.fst"
                                 (Prims.of_int (612)) (Prims.of_int (4))
                                 (Prims.of_int (615)) (Prims.of_int (93)))
                              (Prims.mk_range
                                 "FStar.InteractiveHelpers.PostProcess.fst"
                                 (Prims.of_int (625)) (Prims.of_int (2))
                                 (Prims.of_int (739)) (Prims.of_int (30)))
                              (FStar_Tactics_Effect.lift_div_tac
                                 (fun uu___1 ->
                                    fun uu___2 ->
                                      FStar_Tactics_Effect.tac_bind
                                        (Prims.mk_range
                                           "FStar.InteractiveHelpers.PostProcess.fst"
                                           (Prims.of_int (612))
                                           (Prims.of_int (10))
                                           (Prims.of_int (612))
                                           (Prims.of_int (39)))
                                        (Prims.mk_range
                                           "FStar.InteractiveHelpers.PostProcess.fst"
                                           (Prims.of_int (612))
                                           (Prims.of_int (4))
                                           (Prims.of_int (615))
                                           (Prims.of_int (93)))
                                        (Obj.magic
                                           (find_focused_in_term ares.res))
                                        (fun uu___3 ->
                                           (fun uu___3 ->
                                              match uu___3 with
                                              | FStar_Pervasives_Native.Some
                                                  res ->
                                                  Obj.magic
                                                    (Obj.repr
                                                       (FStar_Tactics_Effect.lift_div_tac
                                                          (fun uu___4 ->
                                                             ((ares.res),
                                                               res,
                                                               (fun uu___5 ->
                                                                  (fun x ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    x)))
                                                                    uu___5),
                                                               true))))
                                              | FStar_Pervasives_Native.None
                                                  ->
                                                  Obj.magic
                                                    (Obj.repr
                                                       (FStar_InteractiveHelpers_Base.mfail
                                                          "unfold_in_assert_or_assume: could not find a focused term in the assert")))
                                             uu___3)))
                              (fun uu___1 ->
                                 (fun find_in_whole_term ->
                                    Obj.magic
                                      (FStar_Tactics_Effect.tac_bind
                                         (Prims.mk_range
                                            "FStar.InteractiveHelpers.PostProcess.fst"
                                            (Prims.of_int (626))
                                            (Prims.of_int (4))
                                            (Prims.of_int (653))
                                            (Prims.of_int (27)))
                                         (Prims.mk_range
                                            "FStar.InteractiveHelpers.PostProcess.fst"
                                            (Prims.of_int (625))
                                            (Prims.of_int (2))
                                            (Prims.of_int (739))
                                            (Prims.of_int (30)))
                                         (Obj.magic
                                            (FStar_Tactics_Effect.tac_bind
                                               (Prims.mk_range
                                                  "FStar.InteractiveHelpers.PostProcess.fst"
                                                  (Prims.of_int (626))
                                                  (Prims.of_int (12))
                                                  (Prims.of_int (626))
                                                  (Prims.of_int (67)))
                                               (Prims.mk_range
                                                  "FStar.InteractiveHelpers.PostProcess.fst"
                                                  (Prims.of_int (627))
                                                  (Prims.of_int (4))
                                                  (Prims.of_int (653))
                                                  (Prims.of_int (27)))
                                               (Obj.magic
                                                  (FStar_Tactics_Effect.tac_bind
                                                     (Prims.mk_range
                                                        "FStar.InteractiveHelpers.PostProcess.fst"
                                                        (Prims.of_int (626))
                                                        (Prims.of_int (26))
                                                        (Prims.of_int (626))
                                                        (Prims.of_int (67)))
                                                     (Prims.mk_range
                                                        "FStar.InteractiveHelpers.PostProcess.fst"
                                                        (Prims.of_int (626))
                                                        (Prims.of_int (12))
                                                        (Prims.of_int (626))
                                                        (Prims.of_int (67)))
                                                     (Obj.magic
                                                        (FStar_Tactics_Effect.tac_bind
                                                           (Prims.mk_range
                                                              "FStar.InteractiveHelpers.PostProcess.fst"
                                                              (Prims.of_int (626))
                                                              (Prims.of_int (43))
                                                              (Prims.of_int (626))
                                                              (Prims.of_int (66)))
                                                           (Prims.mk_range
                                                              "prims.fst"
                                                              (Prims.of_int (606))
                                                              (Prims.of_int (19))
                                                              (Prims.of_int (606))
                                                              (Prims.of_int (31)))
                                                           (Obj.magic
                                                              (FStar_Tactics_Builtins.term_to_string
                                                                 ares.res))
                                                           (fun uu___1 ->
                                                              FStar_Tactics_Effect.lift_div_tac
                                                                (fun uu___2
                                                                   ->
                                                                   Prims.strcat
                                                                    "Assertion: "
                                                                    uu___1))))
                                                     (fun uu___1 ->
                                                        (fun uu___1 ->
                                                           Obj.magic
                                                             (FStar_InteractiveHelpers_Base.print_dbg
                                                                dbg uu___1))
                                                          uu___1)))
                                               (fun uu___1 ->
                                                  (fun uu___1 ->
                                                     Obj.magic
                                                       (FStar_Tactics_Effect.tac_bind
                                                          (Prims.mk_range
                                                             "FStar.InteractiveHelpers.PostProcess.fst"
                                                             (Prims.of_int (627))
                                                             (Prims.of_int (10))
                                                             (Prims.of_int (627))
                                                             (Prims.of_int (28)))
                                                          (Prims.mk_range
                                                             "FStar.InteractiveHelpers.PostProcess.fst"
                                                             (Prims.of_int (627))
                                                             (Prims.of_int (4))
                                                             (Prims.of_int (653))
                                                             (Prims.of_int (27)))
                                                          (Obj.magic
                                                             (is_eq dbg
                                                                ares.res))
                                                          (fun uu___2 ->
                                                             (fun uu___2 ->
                                                                match uu___2
                                                                with
                                                                | FStar_Pervasives_Native.Some
                                                                    (kd, l,
                                                                    r) ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (629))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (629))
                                                                    (Prims.of_int (50)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (630))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (649))
                                                                    (Prims.of_int (11)))
                                                                    (Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    "The assertion is an equality"))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (630))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (630))
                                                                    (Prims.of_int (40)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (630))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (649))
                                                                    (Prims.of_int (11)))
                                                                    (Obj.magic
                                                                    (find_focused_in_term
                                                                    l))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    match uu___4
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    res ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (632))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (635))
                                                                    (Prims.of_int (64)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (637))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (637))
                                                                    (Prims.of_int (29)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (632))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (635))
                                                                    (Prims.of_int (64)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (632))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (635))
                                                                    (Prims.of_int (64)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (633))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (635))
                                                                    (Prims.of_int (63)))
                                                                    (Prims.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (606))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (606))
                                                                    (Prims.of_int (31)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (633))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (635))
                                                                    (Prims.of_int (63)))
                                                                    (Prims.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (606))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (606))
                                                                    (Prims.of_int (31)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (633))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (633))
                                                                    (Prims.of_int (57)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (633))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (635))
                                                                    (Prims.of_int (63)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Builtins.term_to_string
                                                                    l))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (634))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (635))
                                                                    (Prims.of_int (63)))
                                                                    (Prims.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (606))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (606))
                                                                    (Prims.of_int (31)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (634))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (635))
                                                                    (Prims.of_int (63)))
                                                                    (Prims.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (606))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (606))
                                                                    (Prims.of_int (31)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (634))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (634))
                                                                    (Prims.of_int (57)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (634))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (635))
                                                                    (Prims.of_int (63)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Builtins.term_to_string
                                                                    r))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    uu___6 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (635))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (635))
                                                                    (Prims.of_int (63)))
                                                                    (Prims.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (606))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (606))
                                                                    (Prims.of_int (31)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (635))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (635))
                                                                    (Prims.of_int (63)))
                                                                    (Prims.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (606))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (606))
                                                                    (Prims.of_int (31)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Builtins.term_to_string
                                                                    res.res))
                                                                    (fun
                                                                    uu___7 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    Prims.strcat
                                                                    "\n- focused: "
                                                                    uu___7))))
                                                                    (fun
                                                                    uu___7 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    Prims.strcat
                                                                    uu___6
                                                                    uu___7))))
                                                                    uu___6)))
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    Prims.strcat
                                                                    "\n- right  : "
                                                                    uu___6))))
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    Prims.strcat
                                                                    uu___5
                                                                    uu___6))))
                                                                    uu___5)))
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    Prims.strcat
                                                                    "\n- left   : "
                                                                    uu___5))))
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    Prims.strcat
                                                                    "Found focused term in left operand:"
                                                                    uu___5))))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    uu___5))
                                                                    uu___5)))
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    (l, res,
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun t ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    mk_eq kd
                                                                    t r)))
                                                                    uu___7),
                                                                    true))))
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (639))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (639))
                                                                    (Prims.of_int (42)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (639))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (648))
                                                                    (Prims.of_int (89)))
                                                                    (Obj.magic
                                                                    (find_focused_in_term
                                                                    r))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    match uu___5
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    res ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (641))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (644))
                                                                    (Prims.of_int (58)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (646))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (646))
                                                                    (Prims.of_int (32)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (641))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (644))
                                                                    (Prims.of_int (58)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (641))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (644))
                                                                    (Prims.of_int (58)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (642))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (644))
                                                                    (Prims.of_int (57)))
                                                                    (Prims.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (606))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (606))
                                                                    (Prims.of_int (31)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (642))
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (644))
                                                                    (Prims.of_int (57)))
                                                                    (Prims.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (606))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (606))
                                                                    (Prims.of_int (31)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (642))
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (642))
                                                                    (Prims.of_int (51)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (642))
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (644))
                                                                    (Prims.of_int (57)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Builtins.term_to_string
                                                                    l))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    uu___6 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (643))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (644))
                                                                    (Prims.of_int (57)))
                                                                    (Prims.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (606))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (606))
                                                                    (Prims.of_int (31)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (643))
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (644))
                                                                    (Prims.of_int (57)))
                                                                    (Prims.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (606))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (606))
                                                                    (Prims.of_int (31)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (643))
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (643))
                                                                    (Prims.of_int (51)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (643))
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (644))
                                                                    (Prims.of_int (57)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Builtins.term_to_string
                                                                    r))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    uu___7 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (644))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (644))
                                                                    (Prims.of_int (57)))
                                                                    (Prims.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (606))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (606))
                                                                    (Prims.of_int (31)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (644))
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (644))
                                                                    (Prims.of_int (57)))
                                                                    (Prims.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (606))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (606))
                                                                    (Prims.of_int (31)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Builtins.term_to_string
                                                                    res.res))
                                                                    (fun
                                                                    uu___8 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    Prims.strcat
                                                                    "\n- focused: "
                                                                    uu___8))))
                                                                    (fun
                                                                    uu___8 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    Prims.strcat
                                                                    uu___7
                                                                    uu___8))))
                                                                    uu___7)))
                                                                    (fun
                                                                    uu___7 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    Prims.strcat
                                                                    "\n- right  : "
                                                                    uu___7))))
                                                                    (fun
                                                                    uu___7 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    Prims.strcat
                                                                    uu___6
                                                                    uu___7))))
                                                                    uu___6)))
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    Prims.strcat
                                                                    "\n- left   : "
                                                                    uu___6))))
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    Prims.strcat
                                                                    "Found focused term in right operand:"
                                                                    uu___6))))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    uu___6 ->
                                                                    Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    uu___6))
                                                                    uu___6)))
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    (r, res,
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun t ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    mk_eq kd
                                                                    l t)))
                                                                    uu___8),
                                                                    false))))
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.mfail
                                                                    "unfold_in_assert_or_assume: could not find a focused term in the assert"))
                                                                    uu___5)))
                                                                    uu___4)))
                                                                    uu___3))
                                                                | FStar_Pervasives_Native.None
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (652))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (652))
                                                                    (Prims.of_int (54)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (653))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (653))
                                                                    (Prims.of_int (27)))
                                                                    (Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    "The assertion is not an equality"))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    Obj.magic
                                                                    (find_in_whole_term
                                                                    ()))
                                                                    uu___3)))
                                                               uu___2)))
                                                    uu___1)))
                                         (fun uu___1 ->
                                            (fun uu___1 ->
                                               match uu___1 with
                                               | (subterm, unf_res, rebuild,
                                                  insert_before) ->
                                                   Obj.magic
                                                     (FStar_Tactics_Effect.tac_bind
                                                        (Prims.mk_range
                                                           "FStar.InteractiveHelpers.PostProcess.fst"
                                                           (Prims.of_int (655))
                                                           (Prims.of_int (2))
                                                           (Prims.of_int (739))
                                                           (Prims.of_int (30)))
                                                        (Prims.mk_range
                                                           "FStar.InteractiveHelpers.PostProcess.fst"
                                                           (Prims.of_int (655))
                                                           (Prims.of_int (2))
                                                           (Prims.of_int (739))
                                                           (Prims.of_int (30)))
                                                        (FStar_Tactics_Effect.lift_div_tac
                                                           (fun uu___2 ->
                                                              rebuild))
                                                        (fun uu___2 ->
                                                           (fun rebuild1 ->
                                                              Obj.magic
                                                                (FStar_Tactics_Effect.tac_bind
                                                                   (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (655))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (657))
                                                                    (Prims.of_int (65)))
                                                                   (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (659))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (739))
                                                                    (Prims.of_int (30)))
                                                                   (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (655))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (657))
                                                                    (Prims.of_int (65)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (655))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (657))
                                                                    (Prims.of_int (65)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (656))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (657))
                                                                    (Prims.of_int (64)))
                                                                    (Prims.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (606))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (606))
                                                                    (Prims.of_int (31)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (656))
                                                                    (Prims.of_int (33))
                                                                    (Prims.of_int (657))
                                                                    (Prims.of_int (64)))
                                                                    (Prims.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (606))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (606))
                                                                    (Prims.of_int (31)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (656))
                                                                    (Prims.of_int (33))
                                                                    (Prims.of_int (656))
                                                                    (Prims.of_int (55)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (656))
                                                                    (Prims.of_int (33))
                                                                    (Prims.of_int (657))
                                                                    (Prims.of_int (64)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Builtins.term_to_string
                                                                    subterm))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    uu___2 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (656))
                                                                    (Prims.of_int (58))
                                                                    (Prims.of_int (657))
                                                                    (Prims.of_int (64)))
                                                                    (Prims.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (606))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (606))
                                                                    (Prims.of_int (31)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (657))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (657))
                                                                    (Prims.of_int (64)))
                                                                    (Prims.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (606))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (606))
                                                                    (Prims.of_int (31)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (657))
                                                                    (Prims.of_int (38))
                                                                    (Prims.of_int (657))
                                                                    (Prims.of_int (64)))
                                                                    (Prims.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (606))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (606))
                                                                    (Prims.of_int (31)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Builtins.term_to_string
                                                                    unf_res.res))
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    Prims.strcat
                                                                    "- focused term: "
                                                                    uu___3))))
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    Prims.strcat
                                                                    "\n"
                                                                    uu___3))))
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    Prims.strcat
                                                                    uu___2
                                                                    uu___3))))
                                                                    uu___2)))
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    Prims.strcat
                                                                    "- subterm: "
                                                                    uu___2))))
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    Prims.strcat
                                                                    "Found subterm in assertion/assumption:\n"
                                                                    uu___2))))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    uu___2 ->
                                                                    Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    uu___2))
                                                                    uu___2)))
                                                                   (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    uu___2 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (659))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (659))
                                                                    (Prims.of_int (36)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (660))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (739))
                                                                    (Prims.of_int (30)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Builtins.inspect
                                                                    unf_res.res))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    res_view
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (661))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (700))
                                                                    (Prims.of_int (19)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (660))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (739))
                                                                    (Prims.of_int (30)))
                                                                    (match res_view
                                                                    with
                                                                    | 
                                                                    FStar_Reflection_Data.Tv_FVar
                                                                    fv ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (663))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (663))
                                                                    (Prims.of_int (80)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (665))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (668))
                                                                    (Prims.of_int (28)))
                                                                    (Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    (Prims.strcat
                                                                    "The focused term is a top identifier: "
                                                                    (FStar_Reflection_Derived.fv_to_string
                                                                    fv))))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (665))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (665))
                                                                    (Prims.of_int (46)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (666))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (668))
                                                                    (Prims.of_int (28)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Reflection_Derived.flatten_name
                                                                    (FStar_Reflection_Builtins.inspect_fv
                                                                    fv)))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    fname ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (666))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (666))
                                                                    (Prims.of_int (81)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (667))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (668))
                                                                    (Prims.of_int (28)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Builtins.norm_term_env
                                                                    (ares.ge).FStar_InteractiveHelpers_Base.env
                                                                    [
                                                                    FStar_Pervasives.delta_only
                                                                    [fname];
                                                                    FStar_Pervasives.zeta]
                                                                    subterm))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    subterm'
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (667))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (667))
                                                                    (Prims.of_int (70)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (668))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (668))
                                                                    (Prims.of_int (28)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (667))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (667))
                                                                    (Prims.of_int (70)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (667))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (667))
                                                                    (Prims.of_int (70)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (667))
                                                                    (Prims.of_int (46))
                                                                    (Prims.of_int (667))
                                                                    (Prims.of_int (69)))
                                                                    (Prims.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (606))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (606))
                                                                    (Prims.of_int (31)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Builtins.term_to_string
                                                                    subterm'))
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    Prims.strcat
                                                                    "Normalized subterm: "
                                                                    uu___4))))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    uu___4))
                                                                    uu___4)))
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    ((ares.ge),
                                                                    (FStar_Pervasives_Native.Some
                                                                    subterm'))))))
                                                                    uu___4)))
                                                                    uu___4)))
                                                                    uu___3))
                                                                    | 
                                                                    uu___3 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (673))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (673))
                                                                    (Prims.of_int (49)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (674))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (700))
                                                                    (Prims.of_int (19)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_List_Tot_Base.map
                                                                    FStar_Pervasives_Native.snd
                                                                    ares.parents))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    parents
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (675))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (684))
                                                                    (Prims.of_int (14)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (686))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (700))
                                                                    (Prims.of_int (19)))
                                                                    (match res_view
                                                                    with
                                                                    | 
                                                                    FStar_Reflection_Data.Tv_Var
                                                                    bv ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (677))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (677))
                                                                    (Prims.of_int (84)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (679))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (681))
                                                                    (Prims.of_int (17)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (677))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (677))
                                                                    (Prims.of_int (84)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (677))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (677))
                                                                    (Prims.of_int (84)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (677))
                                                                    (Prims.of_int (68))
                                                                    (Prims.of_int (677))
                                                                    (Prims.of_int (83)))
                                                                    (Prims.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (606))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (606))
                                                                    (Prims.of_int (31)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Print.bv_to_string
                                                                    bv))
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    Prims.strcat
                                                                    "The focused term is a local variable: "
                                                                    uu___4))))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    uu___4))
                                                                    uu___4)))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (679))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (680))
                                                                    (Prims.of_int (106)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (681))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (681))
                                                                    (Prims.of_int (17)))
                                                                    (if
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
                                                                    uu___6 ->
                                                                    ()))))
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Pervasives_Native.Some
                                                                    bv))))
                                                                    uu___4))
                                                                    | 
                                                                    uu___4 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (683))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (683))
                                                                    (Prims.of_int (96)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (684))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (684))
                                                                    (Prims.of_int (14)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (683))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (683))
                                                                    (Prims.of_int (96)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (683))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (683))
                                                                    (Prims.of_int (96)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (683))
                                                                    (Prims.of_int (69))
                                                                    (Prims.of_int (683))
                                                                    (Prims.of_int (95)))
                                                                    (Prims.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (606))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (606))
                                                                    (Prims.of_int (31)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Builtins.term_to_string
                                                                    unf_res.res))
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    Prims.strcat
                                                                    "The focused term is an arbitrary term: "
                                                                    uu___5))))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    uu___5))
                                                                    uu___5)))
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Pervasives_Native.None))))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    opt_bv ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (686))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (686))
                                                                    (Prims.of_int (79)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (686))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (700))
                                                                    (Prims.of_int (19)))
                                                                    (Obj.magic
                                                                    (find_context_equality
                                                                    dbg
                                                                    ares.ge
                                                                    unf_res.res
                                                                    parents
                                                                    []))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    match uu___4
                                                                    with
                                                                    | 
                                                                    (ge1,
                                                                    eq_tm) ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (689))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (691))
                                                                    (Prims.of_int (19)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (694))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (700))
                                                                    (Prims.of_int (19)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    match eq_tm
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    eq_tm1 ->
                                                                    FStar_Pervasives_Native.Some
                                                                    eq_tm1
                                                                    | 
                                                                    uu___6 ->
                                                                    FStar_Pervasives_Native.None))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    opt_eq_tm
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (695))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (698))
                                                                    (Prims.of_int (19)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (700))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (700))
                                                                    (Prims.of_int (19)))
                                                                    (match 
                                                                    (opt_bv,
                                                                    opt_eq_tm)
                                                                    with
                                                                    | 
                                                                    (FStar_Pervasives_Native.Some
                                                                    bv,
                                                                    FStar_Pervasives_Native.Some
                                                                    eq_tm1)
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (696))
                                                                    (Prims.of_int (38))
                                                                    (Prims.of_int (696))
                                                                    (Prims.of_int (81)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (696))
                                                                    (Prims.of_int (33))
                                                                    (Prims.of_int (696))
                                                                    (Prims.of_int (81)))
                                                                    (Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.apply_subst
                                                                    ge1.FStar_InteractiveHelpers_Base.env
                                                                    subterm
                                                                    [
                                                                    (bv,
                                                                    eq_tm1)]))
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Pervasives_Native.Some
                                                                    uu___5))))
                                                                    | 
                                                                    (FStar_Pervasives_Native.None,
                                                                    FStar_Pervasives_Native.Some
                                                                    eq_tm1)
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (697))
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (697))
                                                                    (Prims.of_int (82)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (697))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (697))
                                                                    (Prims.of_int (82)))
                                                                    (Obj.magic
                                                                    (replace_term_in
                                                                    dbg
                                                                    unf_res.res
                                                                    eq_tm1
                                                                    subterm))
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Pervasives_Native.Some
                                                                    uu___5))))
                                                                    | 
                                                                    uu___5 ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Pervasives_Native.None))))
                                                                    (fun
                                                                    subterm'
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    (ge1,
                                                                    subterm')))))
                                                                    uu___5)))
                                                                    uu___4)))
                                                                    uu___4)))
                                                                    uu___4)))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    uu___3 ->
                                                                    match uu___3
                                                                    with
                                                                    | 
                                                                    (ge1,
                                                                    opt_unf_tm)
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (711))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (727))
                                                                    (Prims.of_int (9)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (710))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (739))
                                                                    (Prims.of_int (30)))
                                                                    (match opt_unf_tm
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    unf_tm ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    (ge1,
                                                                    unf_tm))))
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (714))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (714))
                                                                    (Prims.of_int (65)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (714))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (726))
                                                                    (Prims.of_int (42)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (714))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (714))
                                                                    (Prims.of_int (65)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (714))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (714))
                                                                    (Prims.of_int (65)))
                                                                    (Obj.magic
                                                                    (strip_implicit_parameters
                                                                    unf_res.res))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Builtins.inspect
                                                                    uu___4))
                                                                    uu___4)))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    match uu___4
                                                                    with
                                                                    | 
                                                                    FStar_Reflection_Data.Tv_FVar
                                                                    fv ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (716))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (717))
                                                                    (Prims.of_int (41)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (719))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (722))
                                                                    (Prims.of_int (21)))
                                                                    (Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    (Prims.strcat
                                                                    "The focused term is a top identifier with implicit parameters: "
                                                                    (FStar_Reflection_Derived.fv_to_string
                                                                    fv))))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (719))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (719))
                                                                    (Prims.of_int (48)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (720))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (722))
                                                                    (Prims.of_int (21)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Reflection_Derived.flatten_name
                                                                    (FStar_Reflection_Builtins.inspect_fv
                                                                    fv)))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    fname ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (720))
                                                                    (Prims.of_int (23))
                                                                    (Prims.of_int (720))
                                                                    (Prims.of_int (79)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (721))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (722))
                                                                    (Prims.of_int (21)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Builtins.norm_term_env
                                                                    ge1.FStar_InteractiveHelpers_Base.env
                                                                    [
                                                                    FStar_Pervasives.delta_only
                                                                    [fname];
                                                                    FStar_Pervasives.zeta]
                                                                    subterm))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    subterm'
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (721))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (721))
                                                                    (Prims.of_int (72)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (722))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (722))
                                                                    (Prims.of_int (21)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (721))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (721))
                                                                    (Prims.of_int (72)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (721))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (721))
                                                                    (Prims.of_int (72)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (721))
                                                                    (Prims.of_int (48))
                                                                    (Prims.of_int (721))
                                                                    (Prims.of_int (71)))
                                                                    (Prims.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (606))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (606))
                                                                    (Prims.of_int (31)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Builtins.term_to_string
                                                                    subterm'))
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    Prims.strcat
                                                                    "Normalized subterm: "
                                                                    uu___6))))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    uu___6 ->
                                                                    Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    uu___6))
                                                                    uu___6)))
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    (ge1,
                                                                    subterm')))))
                                                                    uu___6)))
                                                                    uu___6)))
                                                                    uu___5))
                                                                    | 
                                                                    uu___5 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (724))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (726))
                                                                    (Prims.of_int (42)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (724))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (726))
                                                                    (Prims.of_int (42)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (725))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (726))
                                                                    (Prims.of_int (41)))
                                                                    (Prims.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (606))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (606))
                                                                    (Prims.of_int (31)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (726))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (726))
                                                                    (Prims.of_int (41)))
                                                                    (Prims.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (606))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (606))
                                                                    (Prims.of_int (31)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Builtins.term_to_string
                                                                    unf_res.res))
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    Prims.strcat
                                                                    "couldn't find equalities with which to rewrite: "
                                                                    uu___6))))
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    Prims.strcat
                                                                    "unfold_in_assert_or_assume: "
                                                                    uu___6))))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    uu___6 ->
                                                                    Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.mfail
                                                                    uu___6))
                                                                    uu___6)))
                                                                    uu___4))))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    match uu___4
                                                                    with
                                                                    | 
                                                                    (ge2,
                                                                    unf_tm)
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (730))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (730))
                                                                    (Prims.of_int (35)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (731))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (739))
                                                                    (Prims.of_int (30)))
                                                                    (Obj.magic
                                                                    (rebuild1
                                                                    unf_tm))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    final_assert
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (731))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (731))
                                                                    (Prims.of_int (51)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (732))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (739))
                                                                    (Prims.of_int (30)))
                                                                    (Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.prettify_term
                                                                    dbg
                                                                    final_assert))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    final_assert1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (732))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (732))
                                                                    (Prims.of_int (71)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (733))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (739))
                                                                    (Prims.of_int (30)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (732))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (732))
                                                                    (Prims.of_int (71)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (732))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (732))
                                                                    (Prims.of_int (71)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (732))
                                                                    (Prims.of_int (43))
                                                                    (Prims.of_int (732))
                                                                    (Prims.of_int (70)))
                                                                    (Prims.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (606))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (606))
                                                                    (Prims.of_int (31)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Builtins.term_to_string
                                                                    final_assert1))
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    Prims.strcat
                                                                    "-> Final assertion:\n"
                                                                    uu___5))))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.print_dbg
                                                                    dbg
                                                                    uu___5))
                                                                    uu___5)))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (734))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (734))
                                                                    (Prims.of_int (94)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (737))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (739))
                                                                    (Prims.of_int (30)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    if
                                                                    insert_before
                                                                    then
                                                                    FStar_InteractiveHelpers_Propositions.mk_assertions
                                                                    [final_assert1]
                                                                    []
                                                                    else
                                                                    FStar_InteractiveHelpers_Propositions.mk_assertions
                                                                    []
                                                                    [final_assert1]))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    asserts
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (737))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (737))
                                                                    (Prims.of_int (79)))
                                                                    (Prims.mk_range
                                                                    "FStar.InteractiveHelpers.PostProcess.fst"
                                                                    (Prims.of_int (737))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (739))
                                                                    (Prims.of_int (30)))
                                                                    (Obj.magic
                                                                    (FStar_InteractiveHelpers_Output.subst_shadowed_with_abs_in_assertions
                                                                    dbg ge2
                                                                    FStar_Pervasives_Native.None
                                                                    asserts))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    uu___6 ->
                                                                    match uu___6
                                                                    with
                                                                    | 
                                                                    (ge3,
                                                                    asserts1)
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_InteractiveHelpers_Output.printout_success
                                                                    ge3
                                                                    asserts1))
                                                                    uu___6)))
                                                                    uu___6)))
                                                                    uu___5)))
                                                                    uu___5)))
                                                                    uu___5)))
                                                                    uu___4)))
                                                                    uu___3)))
                                                                    uu___3)))
                                                                    uu___2)))
                                                             uu___2))) uu___1)))
                                   uu___1))) uu___1))) uu___)
let (pp_unfold_in_assert_or_assume :
  Prims.bool -> unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun dbg ->
    fun uu___ ->
      FStar_Tactics_Derived.try_with
        (fun uu___1 ->
           match () with
           | () ->
               FStar_Tactics_Effect.tac_bind
                 (Prims.mk_range "FStar.InteractiveHelpers.PostProcess.fst"
                    (Prims.of_int (745)) (Prims.of_int (14))
                    (Prims.of_int (745)) (Prims.of_int (53)))
                 (Prims.mk_range "FStar.InteractiveHelpers.PostProcess.fst"
                    (Prims.of_int (746)) (Prims.of_int (4))
                    (Prims.of_int (747)) (Prims.of_int (16)))
                 (Obj.magic (find_focused_assert_in_current_goal dbg))
                 (fun uu___2 ->
                    (fun res ->
                       Obj.magic
                         (FStar_Tactics_Effect.tac_bind
                            (Prims.mk_range
                               "FStar.InteractiveHelpers.PostProcess.fst"
                               (Prims.of_int (746)) (Prims.of_int (4))
                               (Prims.of_int (746)) (Prims.of_int (38)))
                            (Prims.mk_range
                               "FStar.InteractiveHelpers.PostProcess.fst"
                               (Prims.of_int (747)) (Prims.of_int (4))
                               (Prims.of_int (747)) (Prims.of_int (16)))
                            (Obj.magic (unfold_in_assert_or_assume dbg res))
                            (fun uu___2 ->
                               (fun uu___2 -> Obj.magic (end_proof ()))
                                 uu___2))) uu___2))
        (fun uu___1 ->
           match uu___1 with
           | FStar_InteractiveHelpers_Base.MetaAnalysis msg ->
               FStar_Tactics_Effect.tac_bind
                 (Prims.mk_range "FStar.InteractiveHelpers.PostProcess.fst"
                    (Prims.of_int (748)) (Prims.of_int (29))
                    (Prims.of_int (748)) (Prims.of_int (49)))
                 (Prims.mk_range "FStar.InteractiveHelpers.PostProcess.fst"
                    (Prims.of_int (748)) (Prims.of_int (51))
                    (Prims.of_int (748)) (Prims.of_int (63)))
                 (Obj.magic
                    (FStar_InteractiveHelpers_Output.printout_failure msg))
                 (fun uu___2 ->
                    (fun uu___2 -> Obj.magic (end_proof ())) uu___2)
           | err -> FStar_Tactics_Effect.raise err)
let _ =
  FStar_Tactics_Native.register_tactic
    "FStar.InteractiveHelpers.PostProcess.pp_unfold_in_assert_or_assume"
    (Prims.of_int (3))
    (fun psc ->
       fun ncb ->
         fun args ->
           FStar_Tactics_InterpFuns.mk_tactic_interpretation_2
             (FStar_Tactics_Native.from_tactic_2
                pp_unfold_in_assert_or_assume) FStar_Syntax_Embeddings.e_bool
             FStar_Syntax_Embeddings.e_unit FStar_Syntax_Embeddings.e_unit
             psc ncb args)