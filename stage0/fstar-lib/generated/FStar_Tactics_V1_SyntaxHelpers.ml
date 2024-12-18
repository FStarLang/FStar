open Prims
let rec (collect_arr' :
  FStarC_Reflection_Types.binder Prims.list ->
    FStarC_Reflection_Types.comp ->
      ((FStarC_Reflection_Types.binder Prims.list *
         FStarC_Reflection_Types.comp),
        unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun bs ->
         fun c ->
           match FStarC_Reflection_V1_Builtins.inspect_comp c with
           | FStarC_Reflection_V1_Data.C_Total t ->
               Obj.magic
                 (Obj.repr
                    (let uu___ = FStarC_Tactics_V1_Builtins.inspect t in
                     FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "FStar.Tactics.V1.SyntaxHelpers.fst"
                                (Prims.of_int (14)) (Prims.of_int (20))
                                (Prims.of_int (14)) (Prims.of_int (29)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "FStar.Tactics.V1.SyntaxHelpers.fst"
                                (Prims.of_int (14)) (Prims.of_int (14))
                                (Prims.of_int (18)) (Prims.of_int (19)))))
                       (Obj.magic uu___)
                       (fun uu___1 ->
                          (fun uu___1 ->
                             match uu___1 with
                             | FStarC_Reflection_V1_Data.Tv_Arrow (b, c1) ->
                                 Obj.magic
                                   (Obj.repr (collect_arr' (b :: bs) c1))
                             | uu___2 ->
                                 Obj.magic
                                   (Obj.repr
                                      (FStar_Tactics_Effect.lift_div_tac
                                         (fun uu___3 -> (bs, c))))) uu___1)))
           | uu___ ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.lift_div_tac
                       (fun uu___1 -> (bs, c))))) uu___1 uu___
let (collect_arr_bs :
  FStarC_Reflection_Types.typ ->
    ((FStarC_Reflection_Types.binder Prims.list *
       FStarC_Reflection_Types.comp),
      unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    let uu___ =
      collect_arr' []
        (FStarC_Reflection_V1_Builtins.pack_comp
           (FStarC_Reflection_V1_Data.C_Total t)) in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V1.SyntaxHelpers.fst"
               (Prims.of_int (25)) (Prims.of_int (18)) (Prims.of_int (25))
               (Prims.of_int (57)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V1.SyntaxHelpers.fst"
               (Prims.of_int (24)) (Prims.of_int (22)) (Prims.of_int (26))
               (Prims.of_int (29))))) (Obj.magic uu___)
      (fun uu___1 ->
         FStar_Tactics_Effect.lift_div_tac
           (fun uu___2 ->
              match uu___1 with
              | (bs, c) -> ((FStar_List_Tot_Base.rev bs), c)))
let (collect_arr :
  FStarC_Reflection_Types.typ ->
    ((FStarC_Reflection_Types.typ Prims.list * FStarC_Reflection_Types.comp),
      unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    let uu___ =
      collect_arr' []
        (FStarC_Reflection_V1_Builtins.pack_comp
           (FStarC_Reflection_V1_Data.C_Total t)) in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V1.SyntaxHelpers.fst"
               (Prims.of_int (30)) (Prims.of_int (18)) (Prims.of_int (30))
               (Prims.of_int (57)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V1.SyntaxHelpers.fst"
               (Prims.of_int (29)) (Prims.of_int (19)) (Prims.of_int (32))
               (Prims.of_int (29))))) (Obj.magic uu___)
      (fun uu___1 ->
         FStar_Tactics_Effect.lift_div_tac
           (fun uu___2 ->
              match uu___1 with
              | (bs, c) ->
                  ((FStar_List_Tot_Base.rev
                      (FStar_List_Tot_Base.map
                         FStar_Reflection_V1_Derived.type_of_binder bs)), c)))
let rec (collect_abs' :
  FStarC_Reflection_Types.binder Prims.list ->
    FStarC_Reflection_Types.term ->
      ((FStarC_Reflection_Types.binder Prims.list *
         FStarC_Reflection_Types.term),
        unit) FStar_Tactics_Effect.tac_repr)
  =
  fun bs ->
    fun t ->
      let uu___ = FStarC_Tactics_V1_Builtins.inspect t in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.V1.SyntaxHelpers.fst"
                 (Prims.of_int (36)) (Prims.of_int (10)) (Prims.of_int (36))
                 (Prims.of_int (19)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.V1.SyntaxHelpers.fst"
                 (Prims.of_int (36)) (Prims.of_int (4)) (Prims.of_int (39))
                 (Prims.of_int (18))))) (Obj.magic uu___)
        (fun uu___1 ->
           (fun uu___1 ->
              match uu___1 with
              | FStarC_Reflection_V1_Data.Tv_Abs (b, t') ->
                  Obj.magic (Obj.repr (collect_abs' (b :: bs) t'))
              | uu___2 ->
                  Obj.magic
                    (Obj.repr
                       (FStar_Tactics_Effect.lift_div_tac
                          (fun uu___3 -> (bs, t))))) uu___1)
let (collect_abs :
  FStarC_Reflection_Types.term ->
    ((FStarC_Reflection_Types.binder Prims.list *
       FStarC_Reflection_Types.term),
      unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    let uu___ = collect_abs' [] t in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V1.SyntaxHelpers.fst"
               (Prims.of_int (43)) (Prims.of_int (19)) (Prims.of_int (43))
               (Prims.of_int (36)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V1.SyntaxHelpers.fst"
               (Prims.of_int (42)) (Prims.of_int (19)) (Prims.of_int (44))
               (Prims.of_int (30))))) (Obj.magic uu___)
      (fun uu___1 ->
         FStar_Tactics_Effect.lift_div_tac
           (fun uu___2 ->
              match uu___1 with
              | (bs, t') -> ((FStar_List_Tot_Base.rev bs), t')))
let fail : 'a . Prims.string -> ('a, unit) FStar_Tactics_Effect.tac_repr =
  fun uu___ ->
    (fun m ->
       Obj.magic
         (FStar_Tactics_Effect.raise
            (FStarC_Tactics_Common.TacticFailure
               ((FStarC_Errors_Msg.mkmsg m), FStar_Pervasives_Native.None))))
      uu___
let rec (mk_arr :
  FStarC_Reflection_Types.binder Prims.list ->
    FStarC_Reflection_Types.comp ->
      (FStarC_Reflection_Types.term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun bs ->
    fun cod ->
      match bs with
      | [] -> fail "mk_arr, empty binders"
      | b::[] ->
          FStarC_Tactics_V1_Builtins.pack
            (FStarC_Reflection_V1_Data.Tv_Arrow (b, cod))
      | b::bs1 ->
          let uu___ =
            let uu___1 =
              let uu___2 =
                let uu___3 = mk_arr bs1 cod in
                FStar_Tactics_Effect.tac_bind
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range
                           "FStar.Tactics.V1.SyntaxHelpers.fst"
                           (Prims.of_int (55)) (Prims.of_int (43))
                           (Prims.of_int (55)) (Prims.of_int (58)))))
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range
                           "FStar.Tactics.V1.SyntaxHelpers.fst"
                           (Prims.of_int (55)) (Prims.of_int (34))
                           (Prims.of_int (55)) (Prims.of_int (59)))))
                  (Obj.magic uu___3)
                  (fun uu___4 ->
                     FStar_Tactics_Effect.lift_div_tac
                       (fun uu___5 ->
                          FStarC_Reflection_V1_Data.C_Total uu___4)) in
              FStar_Tactics_Effect.tac_bind
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range
                         "FStar.Tactics.V1.SyntaxHelpers.fst"
                         (Prims.of_int (55)) (Prims.of_int (34))
                         (Prims.of_int (55)) (Prims.of_int (59)))))
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range
                         "FStar.Tactics.V1.SyntaxHelpers.fst"
                         (Prims.of_int (55)) (Prims.of_int (23))
                         (Prims.of_int (55)) (Prims.of_int (60)))))
                (Obj.magic uu___2)
                (fun uu___3 ->
                   FStar_Tactics_Effect.lift_div_tac
                     (fun uu___4 ->
                        FStarC_Reflection_V1_Builtins.pack_comp uu___3)) in
            FStar_Tactics_Effect.tac_bind
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range
                       "FStar.Tactics.V1.SyntaxHelpers.fst"
                       (Prims.of_int (55)) (Prims.of_int (23))
                       (Prims.of_int (55)) (Prims.of_int (60)))))
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range
                       "FStar.Tactics.V1.SyntaxHelpers.fst"
                       (Prims.of_int (55)) (Prims.of_int (11))
                       (Prims.of_int (55)) (Prims.of_int (61)))))
              (Obj.magic uu___1)
              (fun uu___2 ->
                 FStar_Tactics_Effect.lift_div_tac
                   (fun uu___3 ->
                      FStarC_Reflection_V1_Data.Tv_Arrow (b, uu___2))) in
          FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "FStar.Tactics.V1.SyntaxHelpers.fst"
                     (Prims.of_int (55)) (Prims.of_int (11))
                     (Prims.of_int (55)) (Prims.of_int (61)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "FStar.Tactics.V1.SyntaxHelpers.fst"
                     (Prims.of_int (55)) (Prims.of_int (6))
                     (Prims.of_int (55)) (Prims.of_int (61)))))
            (Obj.magic uu___)
            (fun uu___1 ->
               (fun uu___1 ->
                  Obj.magic (FStarC_Tactics_V1_Builtins.pack uu___1)) uu___1)
let rec (mk_arr_curried :
  FStarC_Reflection_Types.binder Prims.list ->
    FStarC_Reflection_Types.comp ->
      (FStarC_Reflection_Types.term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun bs ->
    fun cod ->
      match bs with
      | [] -> fail "mk_arr, empty binders"
      | b::[] ->
          FStarC_Tactics_V1_Builtins.pack_curried
            (FStarC_Reflection_V1_Data.Tv_Arrow (b, cod))
      | b::bs1 ->
          let uu___ =
            let uu___1 =
              let uu___2 =
                let uu___3 = mk_arr_curried bs1 cod in
                FStar_Tactics_Effect.tac_bind
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range
                           "FStar.Tactics.V1.SyntaxHelpers.fst"
                           (Prims.of_int (61)) (Prims.of_int (62))
                           (Prims.of_int (61)) (Prims.of_int (85)))))
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range
                           "FStar.Tactics.V1.SyntaxHelpers.fst"
                           (Prims.of_int (61)) (Prims.of_int (53))
                           (Prims.of_int (61)) (Prims.of_int (86)))))
                  (Obj.magic uu___3)
                  (fun uu___4 ->
                     FStar_Tactics_Effect.lift_div_tac
                       (fun uu___5 ->
                          FStarC_Reflection_V1_Data.C_Total uu___4)) in
              FStar_Tactics_Effect.tac_bind
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range
                         "FStar.Tactics.V1.SyntaxHelpers.fst"
                         (Prims.of_int (61)) (Prims.of_int (53))
                         (Prims.of_int (61)) (Prims.of_int (86)))))
                (FStar_Sealed.seal
                   (Obj.magic
                      (FStar_Range.mk_range
                         "FStar.Tactics.V1.SyntaxHelpers.fst"
                         (Prims.of_int (61)) (Prims.of_int (42))
                         (Prims.of_int (61)) (Prims.of_int (87)))))
                (Obj.magic uu___2)
                (fun uu___3 ->
                   FStar_Tactics_Effect.lift_div_tac
                     (fun uu___4 ->
                        FStarC_Reflection_V1_Builtins.pack_comp uu___3)) in
            FStar_Tactics_Effect.tac_bind
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range
                       "FStar.Tactics.V1.SyntaxHelpers.fst"
                       (Prims.of_int (61)) (Prims.of_int (42))
                       (Prims.of_int (61)) (Prims.of_int (87)))))
              (FStar_Sealed.seal
                 (Obj.magic
                    (FStar_Range.mk_range
                       "FStar.Tactics.V1.SyntaxHelpers.fst"
                       (Prims.of_int (61)) (Prims.of_int (30))
                       (Prims.of_int (61)) (Prims.of_int (88)))))
              (Obj.magic uu___1)
              (fun uu___2 ->
                 FStar_Tactics_Effect.lift_div_tac
                   (fun uu___3 ->
                      FStarC_Reflection_V1_Data.Tv_Arrow (b, uu___2))) in
          FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "FStar.Tactics.V1.SyntaxHelpers.fst"
                     (Prims.of_int (61)) (Prims.of_int (30))
                     (Prims.of_int (61)) (Prims.of_int (88)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "FStar.Tactics.V1.SyntaxHelpers.fst"
                     (Prims.of_int (61)) (Prims.of_int (17))
                     (Prims.of_int (61)) (Prims.of_int (88)))))
            (Obj.magic uu___)
            (fun uu___1 ->
               (fun uu___1 ->
                  Obj.magic (FStarC_Tactics_V1_Builtins.pack_curried uu___1))
                 uu___1)
let rec (mk_tot_arr :
  FStarC_Reflection_Types.binder Prims.list ->
    FStarC_Reflection_Types.term ->
      (FStarC_Reflection_Types.term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun bs ->
         fun cod ->
           match bs with
           | [] ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> cod)))
           | b::bs1 ->
               Obj.magic
                 (Obj.repr
                    (let uu___ =
                       let uu___1 =
                         let uu___2 =
                           let uu___3 = mk_tot_arr bs1 cod in
                           FStar_Tactics_Effect.tac_bind
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "FStar.Tactics.V1.SyntaxHelpers.fst"
                                      (Prims.of_int (67)) (Prims.of_int (43))
                                      (Prims.of_int (67)) (Prims.of_int (62)))))
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "FStar.Tactics.V1.SyntaxHelpers.fst"
                                      (Prims.of_int (67)) (Prims.of_int (34))
                                      (Prims.of_int (67)) (Prims.of_int (63)))))
                             (Obj.magic uu___3)
                             (fun uu___4 ->
                                FStar_Tactics_Effect.lift_div_tac
                                  (fun uu___5 ->
                                     FStarC_Reflection_V1_Data.C_Total uu___4)) in
                         FStar_Tactics_Effect.tac_bind
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "FStar.Tactics.V1.SyntaxHelpers.fst"
                                    (Prims.of_int (67)) (Prims.of_int (34))
                                    (Prims.of_int (67)) (Prims.of_int (63)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "FStar.Tactics.V1.SyntaxHelpers.fst"
                                    (Prims.of_int (67)) (Prims.of_int (23))
                                    (Prims.of_int (67)) (Prims.of_int (64)))))
                           (Obj.magic uu___2)
                           (fun uu___3 ->
                              FStar_Tactics_Effect.lift_div_tac
                                (fun uu___4 ->
                                   FStarC_Reflection_V1_Builtins.pack_comp
                                     uu___3)) in
                       FStar_Tactics_Effect.tac_bind
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "FStar.Tactics.V1.SyntaxHelpers.fst"
                                  (Prims.of_int (67)) (Prims.of_int (23))
                                  (Prims.of_int (67)) (Prims.of_int (64)))))
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "FStar.Tactics.V1.SyntaxHelpers.fst"
                                  (Prims.of_int (67)) (Prims.of_int (11))
                                  (Prims.of_int (67)) (Prims.of_int (65)))))
                         (Obj.magic uu___1)
                         (fun uu___2 ->
                            FStar_Tactics_Effect.lift_div_tac
                              (fun uu___3 ->
                                 FStarC_Reflection_V1_Data.Tv_Arrow
                                   (b, uu___2))) in
                     FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "FStar.Tactics.V1.SyntaxHelpers.fst"
                                (Prims.of_int (67)) (Prims.of_int (11))
                                (Prims.of_int (67)) (Prims.of_int (65)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "FStar.Tactics.V1.SyntaxHelpers.fst"
                                (Prims.of_int (67)) (Prims.of_int (6))
                                (Prims.of_int (67)) (Prims.of_int (65)))))
                       (Obj.magic uu___)
                       (fun uu___1 ->
                          (fun uu___1 ->
                             Obj.magic
                               (FStarC_Tactics_V1_Builtins.pack uu___1))
                            uu___1)))) uu___1 uu___
let (lookup_lb_view :
  FStarC_Reflection_Types.letbinding Prims.list ->
    FStarC_Reflection_Types.name ->
      (FStarC_Reflection_V1_Data.lb_view, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun lbs ->
    fun nm ->
      let uu___ =
        Obj.magic
          (FStar_Tactics_Effect.lift_div_tac
             (fun uu___1 ->
                FStar_List_Tot_Base.find
                  (fun lb ->
                     (FStarC_Reflection_V1_Builtins.inspect_fv
                        (FStarC_Reflection_V1_Builtins.inspect_lb lb).FStarC_Reflection_V1_Data.lb_fv)
                       = nm) lbs)) in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.V1.SyntaxHelpers.fst"
                 (Prims.of_int (70)) (Prims.of_int (10)) (Prims.of_int (74))
                 (Prims.of_int (16)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.V1.SyntaxHelpers.fst"
                 (Prims.of_int (76)) (Prims.of_int (2)) (Prims.of_int (78))
                 (Prims.of_int (56))))) (Obj.magic uu___)
        (fun uu___1 ->
           (fun o ->
              match o with
              | FStar_Pervasives_Native.Some lb ->
                  Obj.magic
                    (Obj.repr
                       (FStar_Tactics_Effect.lift_div_tac
                          (fun uu___1 ->
                             FStarC_Reflection_V1_Builtins.inspect_lb lb)))
              | FStar_Pervasives_Native.None ->
                  Obj.magic
                    (Obj.repr (fail "lookup_lb_view: Name not in let group")))
             uu___1)
let rec (inspect_unascribe :
  FStarC_Reflection_Types.term ->
    (FStarC_Reflection_V1_Data.term_view, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    let uu___ = FStarC_Tactics_V1_Builtins.inspect t in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V1.SyntaxHelpers.fst"
               (Prims.of_int (81)) (Prims.of_int (8)) (Prims.of_int (81))
               (Prims.of_int (17)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V1.SyntaxHelpers.fst"
               (Prims.of_int (81)) (Prims.of_int (2)) (Prims.of_int (85))
               (Prims.of_int (12))))) (Obj.magic uu___)
      (fun uu___1 ->
         (fun uu___1 ->
            match uu___1 with
            | FStarC_Reflection_V1_Data.Tv_AscribedT
                (t1, uu___2, uu___3, uu___4) ->
                Obj.magic (Obj.repr (inspect_unascribe t1))
            | FStarC_Reflection_V1_Data.Tv_AscribedC
                (t1, uu___2, uu___3, uu___4) ->
                Obj.magic (Obj.repr (inspect_unascribe t1))
            | tv ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.lift_div_tac (fun uu___2 -> tv))))
           uu___1)
let rec (collect_app' :
  FStarC_Reflection_V1_Data.argv Prims.list ->
    FStarC_Reflection_Types.term ->
      ((FStarC_Reflection_Types.term * FStarC_Reflection_V1_Data.argv
         Prims.list),
        unit) FStar_Tactics_Effect.tac_repr)
  =
  fun args ->
    fun t ->
      let uu___ = inspect_unascribe t in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.V1.SyntaxHelpers.fst"
                 (Prims.of_int (90)) (Prims.of_int (10)) (Prims.of_int (90))
                 (Prims.of_int (29)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.V1.SyntaxHelpers.fst"
                 (Prims.of_int (90)) (Prims.of_int (4)) (Prims.of_int (93))
                 (Prims.of_int (20))))) (Obj.magic uu___)
        (fun uu___1 ->
           (fun uu___1 ->
              match uu___1 with
              | FStarC_Reflection_V1_Data.Tv_App (l, r) ->
                  Obj.magic (Obj.repr (collect_app' (r :: args) l))
              | uu___2 ->
                  Obj.magic
                    (Obj.repr
                       (FStar_Tactics_Effect.lift_div_tac
                          (fun uu___3 -> (t, args))))) uu___1)
let (collect_app :
  FStarC_Reflection_Types.term ->
    ((FStarC_Reflection_Types.term * FStarC_Reflection_V1_Data.argv
       Prims.list),
      unit) FStar_Tactics_Effect.tac_repr)
  = collect_app' []