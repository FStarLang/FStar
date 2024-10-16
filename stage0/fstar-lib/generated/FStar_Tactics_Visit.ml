open Prims
let (on_sort_binder :
  (FStarC_Reflection_Types.term ->
     (FStarC_Reflection_Types.term, unit) FStar_Tactics_Effect.tac_repr)
    ->
    FStarC_Reflection_Types.binder ->
      (FStarC_Reflection_Types.binder, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun f ->
    fun b ->
      let uu___ =
        Obj.magic
          (FStar_Tactics_Effect.lift_div_tac
             (fun uu___1 -> FStarC_Reflection_V2_Builtins.inspect_binder b)) in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.Visit.fst"
                 (Prims.of_int (27)) (Prims.of_int (14)) (Prims.of_int (27))
                 (Prims.of_int (30)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.Visit.fst"
                 (Prims.of_int (27)) (Prims.of_int (33)) (Prims.of_int (29))
                 (Prims.of_int (19))))) (Obj.magic uu___)
        (fun uu___1 ->
           (fun bview ->
              let uu___1 =
                let uu___2 = f bview.FStarC_Reflection_V2_Data.sort2 in
                FStar_Tactics_Effect.tac_bind
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range "FStar.Tactics.Visit.fst"
                           (Prims.of_int (28)) (Prims.of_int (34))
                           (Prims.of_int (28)) (Prims.of_int (46)))))
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range "FStar.Tactics.Visit.fst"
                           (Prims.of_int (28)) (Prims.of_int (16))
                           (Prims.of_int (28)) (Prims.of_int (46)))))
                  (Obj.magic uu___2)
                  (fun uu___3 ->
                     FStar_Tactics_Effect.lift_div_tac
                       (fun uu___4 ->
                          {
                            FStarC_Reflection_V2_Data.sort2 = uu___3;
                            FStarC_Reflection_V2_Data.qual =
                              (bview.FStarC_Reflection_V2_Data.qual);
                            FStarC_Reflection_V2_Data.attrs =
                              (bview.FStarC_Reflection_V2_Data.attrs);
                            FStarC_Reflection_V2_Data.ppname2 =
                              (bview.FStarC_Reflection_V2_Data.ppname2)
                          })) in
              Obj.magic
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "FStar.Tactics.Visit.fst"
                            (Prims.of_int (28)) (Prims.of_int (16))
                            (Prims.of_int (28)) (Prims.of_int (46)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "FStar.Tactics.Visit.fst"
                            (Prims.of_int (29)) (Prims.of_int (2))
                            (Prims.of_int (29)) (Prims.of_int (19)))))
                   (Obj.magic uu___1)
                   (fun bview1 ->
                      FStar_Tactics_Effect.lift_div_tac
                        (fun uu___2 ->
                           FStarC_Reflection_V2_Builtins.pack_binder bview1))))
             uu___1)
let (on_sort_simple_binder :
  (FStarC_Reflection_Types.term ->
     (FStarC_Reflection_Types.term, unit) FStar_Tactics_Effect.tac_repr)
    ->
    FStarC_Reflection_V2_Data.simple_binder ->
      (FStarC_Reflection_V2_Data.simple_binder, unit)
        FStar_Tactics_Effect.tac_repr)
  =
  fun f ->
    fun b ->
      let uu___ =
        Obj.magic
          (FStar_Tactics_Effect.lift_div_tac
             (fun uu___1 -> FStarC_Reflection_V2_Builtins.inspect_binder b)) in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.Visit.fst"
                 (Prims.of_int (33)) (Prims.of_int (14)) (Prims.of_int (33))
                 (Prims.of_int (30)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.Visit.fst"
                 (Prims.of_int (33)) (Prims.of_int (33)) (Prims.of_int (36))
                 (Prims.of_int (19))))) (Obj.magic uu___)
        (fun uu___1 ->
           (fun bview ->
              let uu___1 =
                let uu___2 = f bview.FStarC_Reflection_V2_Data.sort2 in
                FStar_Tactics_Effect.tac_bind
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range "FStar.Tactics.Visit.fst"
                           (Prims.of_int (34)) (Prims.of_int (34))
                           (Prims.of_int (34)) (Prims.of_int (46)))))
                  (FStar_Sealed.seal
                     (Obj.magic
                        (FStar_Range.mk_range "FStar.Tactics.Visit.fst"
                           (Prims.of_int (34)) (Prims.of_int (16))
                           (Prims.of_int (34)) (Prims.of_int (46)))))
                  (Obj.magic uu___2)
                  (fun uu___3 ->
                     FStar_Tactics_Effect.lift_div_tac
                       (fun uu___4 ->
                          {
                            FStarC_Reflection_V2_Data.sort2 = uu___3;
                            FStarC_Reflection_V2_Data.qual =
                              (bview.FStarC_Reflection_V2_Data.qual);
                            FStarC_Reflection_V2_Data.attrs =
                              (bview.FStarC_Reflection_V2_Data.attrs);
                            FStarC_Reflection_V2_Data.ppname2 =
                              (bview.FStarC_Reflection_V2_Data.ppname2)
                          })) in
              Obj.magic
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "FStar.Tactics.Visit.fst"
                            (Prims.of_int (34)) (Prims.of_int (16))
                            (Prims.of_int (34)) (Prims.of_int (46)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "FStar.Tactics.Visit.fst"
                            (Prims.of_int (36)) (Prims.of_int (2))
                            (Prims.of_int (36)) (Prims.of_int (19)))))
                   (Obj.magic uu___1)
                   (fun bview1 ->
                      FStar_Tactics_Effect.lift_div_tac
                        (fun uu___2 ->
                           FStarC_Reflection_V2_Builtins.pack_binder bview1))))
             uu___1)
let rec (visit_tm :
  (FStarC_Reflection_Types.term ->
     (FStarC_Reflection_Types.term, unit) FStar_Tactics_Effect.tac_repr)
    ->
    FStarC_Reflection_Types.term ->
      (FStarC_Reflection_Types.term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun ff ->
    fun t ->
      let uu___ =
        Obj.magic
          (FStar_Tactics_Effect.lift_div_tac
             (fun uu___1 -> FStarC_Reflection_V2_Builtins.inspect_ln t)) in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.Visit.fst"
                 (Prims.of_int (39)) (Prims.of_int (11)) (Prims.of_int (39))
                 (Prims.of_int (23)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.Visit.fst"
                 (Prims.of_int (39)) (Prims.of_int (26)) (Prims.of_int (95))
                 (Prims.of_int (18))))) (Obj.magic uu___)
        (fun uu___1 ->
           (fun tv ->
              let uu___1 =
                match tv with
                | FStarC_Reflection_V2_Data.Tv_FVar uu___2 ->
                    Obj.magic
                      (Obj.repr
                         (FStar_Tactics_Effect.lift_div_tac
                            (fun uu___3 -> tv)))
                | FStarC_Reflection_V2_Data.Tv_Var uu___2 ->
                    Obj.magic
                      (Obj.repr
                         (FStar_Tactics_Effect.lift_div_tac
                            (fun uu___3 -> tv)))
                | FStarC_Reflection_V2_Data.Tv_BVar uu___2 ->
                    Obj.magic
                      (Obj.repr
                         (FStar_Tactics_Effect.lift_div_tac
                            (fun uu___3 -> tv)))
                | FStarC_Reflection_V2_Data.Tv_UInst (uu___2, uu___3) ->
                    Obj.magic
                      (Obj.repr
                         (FStar_Tactics_Effect.lift_div_tac
                            (fun uu___4 -> tv)))
                | FStarC_Reflection_V2_Data.Tv_Type u ->
                    Obj.magic
                      (Obj.repr
                         (FStar_Tactics_Effect.lift_div_tac
                            (fun uu___2 ->
                               FStarC_Reflection_V2_Data.Tv_Type u)))
                | FStarC_Reflection_V2_Data.Tv_Const c ->
                    Obj.magic
                      (Obj.repr
                         (FStar_Tactics_Effect.lift_div_tac
                            (fun uu___2 ->
                               FStarC_Reflection_V2_Data.Tv_Const c)))
                | FStarC_Reflection_V2_Data.Tv_Uvar (i, u) ->
                    Obj.magic
                      (Obj.repr
                         (FStar_Tactics_Effect.lift_div_tac
                            (fun uu___2 ->
                               FStarC_Reflection_V2_Data.Tv_Uvar (i, u))))
                | FStarC_Reflection_V2_Data.Tv_Unknown ->
                    Obj.magic
                      (Obj.repr
                         (FStar_Tactics_Effect.lift_div_tac
                            (fun uu___2 ->
                               FStarC_Reflection_V2_Data.Tv_Unknown)))
                | FStarC_Reflection_V2_Data.Tv_Unsupp ->
                    Obj.magic
                      (Obj.repr
                         (FStar_Tactics_Effect.lift_div_tac
                            (fun uu___2 ->
                               FStarC_Reflection_V2_Data.Tv_Unsupp)))
                | FStarC_Reflection_V2_Data.Tv_Arrow (b, c) ->
                    Obj.magic
                      (Obj.repr
                         (let uu___2 = on_sort_binder (visit_tm ff) b in
                          FStar_Tactics_Effect.tac_bind
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.Visit.fst"
                                     (Prims.of_int (53)) (Prims.of_int (16))
                                     (Prims.of_int (53)) (Prims.of_int (46)))))
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.Visit.fst"
                                     (Prims.of_int (53)) (Prims.of_int (49))
                                     (Prims.of_int (55)) (Prims.of_int (20)))))
                            (Obj.magic uu___2)
                            (fun uu___3 ->
                               (fun b1 ->
                                  let uu___3 = visit_comp ff c in
                                  Obj.magic
                                    (FStar_Tactics_Effect.tac_bind
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "FStar.Tactics.Visit.fst"
                                                (Prims.of_int (54))
                                                (Prims.of_int (16))
                                                (Prims.of_int (54))
                                                (Prims.of_int (31)))))
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "FStar.Tactics.Visit.fst"
                                                (Prims.of_int (55))
                                                (Prims.of_int (8))
                                                (Prims.of_int (55))
                                                (Prims.of_int (20)))))
                                       (Obj.magic uu___3)
                                       (fun c1 ->
                                          FStar_Tactics_Effect.lift_div_tac
                                            (fun uu___4 ->
                                               FStarC_Reflection_V2_Data.Tv_Arrow
                                                 (b1, c1))))) uu___3)))
                | FStarC_Reflection_V2_Data.Tv_Abs (b, t1) ->
                    Obj.magic
                      (Obj.repr
                         (let uu___2 = on_sort_binder (visit_tm ff) b in
                          FStar_Tactics_Effect.tac_bind
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.Visit.fst"
                                     (Prims.of_int (57)) (Prims.of_int (16))
                                     (Prims.of_int (57)) (Prims.of_int (46)))))
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.Visit.fst"
                                     (Prims.of_int (57)) (Prims.of_int (49))
                                     (Prims.of_int (59)) (Prims.of_int (18)))))
                            (Obj.magic uu___2)
                            (fun uu___3 ->
                               (fun b1 ->
                                  let uu___3 = visit_tm ff t1 in
                                  Obj.magic
                                    (FStar_Tactics_Effect.tac_bind
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "FStar.Tactics.Visit.fst"
                                                (Prims.of_int (58))
                                                (Prims.of_int (16))
                                                (Prims.of_int (58))
                                                (Prims.of_int (29)))))
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "FStar.Tactics.Visit.fst"
                                                (Prims.of_int (59))
                                                (Prims.of_int (8))
                                                (Prims.of_int (59))
                                                (Prims.of_int (18)))))
                                       (Obj.magic uu___3)
                                       (fun t2 ->
                                          FStar_Tactics_Effect.lift_div_tac
                                            (fun uu___4 ->
                                               FStarC_Reflection_V2_Data.Tv_Abs
                                                 (b1, t2))))) uu___3)))
                | FStarC_Reflection_V2_Data.Tv_App (l, (r, q)) ->
                    Obj.magic
                      (Obj.repr
                         (let uu___2 = visit_tm ff l in
                          FStar_Tactics_Effect.tac_bind
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.Visit.fst"
                                     (Prims.of_int (61)) (Prims.of_int (17))
                                     (Prims.of_int (61)) (Prims.of_int (30)))))
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.Visit.fst"
                                     (Prims.of_int (61)) (Prims.of_int (33))
                                     (Prims.of_int (63)) (Prims.of_int (24)))))
                            (Obj.magic uu___2)
                            (fun uu___3 ->
                               (fun l1 ->
                                  let uu___3 = visit_tm ff r in
                                  Obj.magic
                                    (FStar_Tactics_Effect.tac_bind
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "FStar.Tactics.Visit.fst"
                                                (Prims.of_int (62))
                                                (Prims.of_int (17))
                                                (Prims.of_int (62))
                                                (Prims.of_int (30)))))
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "FStar.Tactics.Visit.fst"
                                                (Prims.of_int (63))
                                                (Prims.of_int (9))
                                                (Prims.of_int (63))
                                                (Prims.of_int (24)))))
                                       (Obj.magic uu___3)
                                       (fun r1 ->
                                          FStar_Tactics_Effect.lift_div_tac
                                            (fun uu___4 ->
                                               FStarC_Reflection_V2_Data.Tv_App
                                                 (l1, (r1, q)))))) uu___3)))
                | FStarC_Reflection_V2_Data.Tv_Refine (b, r) ->
                    Obj.magic
                      (Obj.repr
                         (let uu___2 = on_sort_simple_binder (visit_tm ff) b in
                          FStar_Tactics_Effect.tac_bind
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.Visit.fst"
                                     (Prims.of_int (65)) (Prims.of_int (16))
                                     (Prims.of_int (65)) (Prims.of_int (53)))))
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.Visit.fst"
                                     (Prims.of_int (65)) (Prims.of_int (56))
                                     (Prims.of_int (67)) (Prims.of_int (21)))))
                            (Obj.magic uu___2)
                            (fun uu___3 ->
                               (fun b1 ->
                                  let uu___3 = visit_tm ff r in
                                  Obj.magic
                                    (FStar_Tactics_Effect.tac_bind
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "FStar.Tactics.Visit.fst"
                                                (Prims.of_int (66))
                                                (Prims.of_int (16))
                                                (Prims.of_int (66))
                                                (Prims.of_int (29)))))
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "FStar.Tactics.Visit.fst"
                                                (Prims.of_int (67))
                                                (Prims.of_int (8))
                                                (Prims.of_int (67))
                                                (Prims.of_int (21)))))
                                       (Obj.magic uu___3)
                                       (fun r1 ->
                                          FStar_Tactics_Effect.lift_div_tac
                                            (fun uu___4 ->
                                               FStarC_Reflection_V2_Data.Tv_Refine
                                                 (b1, r1))))) uu___3)))
                | FStarC_Reflection_V2_Data.Tv_Let (r, attrs, b, def, t1) ->
                    Obj.magic
                      (Obj.repr
                         (let uu___2 = on_sort_simple_binder (visit_tm ff) b in
                          FStar_Tactics_Effect.tac_bind
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.Visit.fst"
                                     (Prims.of_int (69)) (Prims.of_int (16))
                                     (Prims.of_int (69)) (Prims.of_int (53)))))
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.Visit.fst"
                                     (Prims.of_int (69)) (Prims.of_int (56))
                                     (Prims.of_int (72)) (Prims.of_int (30)))))
                            (Obj.magic uu___2)
                            (fun uu___3 ->
                               (fun b1 ->
                                  let uu___3 = visit_tm ff def in
                                  Obj.magic
                                    (FStar_Tactics_Effect.tac_bind
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "FStar.Tactics.Visit.fst"
                                                (Prims.of_int (70))
                                                (Prims.of_int (18))
                                                (Prims.of_int (70))
                                                (Prims.of_int (33)))))
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "FStar.Tactics.Visit.fst"
                                                (Prims.of_int (70))
                                                (Prims.of_int (36))
                                                (Prims.of_int (72))
                                                (Prims.of_int (30)))))
                                       (Obj.magic uu___3)
                                       (fun uu___4 ->
                                          (fun def1 ->
                                             let uu___4 = visit_tm ff t1 in
                                             Obj.magic
                                               (FStar_Tactics_Effect.tac_bind
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "FStar.Tactics.Visit.fst"
                                                           (Prims.of_int (71))
                                                           (Prims.of_int (16))
                                                           (Prims.of_int (71))
                                                           (Prims.of_int (29)))))
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "FStar.Tactics.Visit.fst"
                                                           (Prims.of_int (72))
                                                           (Prims.of_int (8))
                                                           (Prims.of_int (72))
                                                           (Prims.of_int (30)))))
                                                  (Obj.magic uu___4)
                                                  (fun t2 ->
                                                     FStar_Tactics_Effect.lift_div_tac
                                                       (fun uu___5 ->
                                                          FStarC_Reflection_V2_Data.Tv_Let
                                                            (r, attrs, b1,
                                                              def1, t2)))))
                                            uu___4))) uu___3)))
                | FStarC_Reflection_V2_Data.Tv_Match (sc, ret_opt, brs) ->
                    Obj.magic
                      (Obj.repr
                         (let uu___2 = visit_tm ff sc in
                          FStar_Tactics_Effect.tac_bind
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.Visit.fst"
                                     (Prims.of_int (74)) (Prims.of_int (17))
                                     (Prims.of_int (74)) (Prims.of_int (31)))))
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.Visit.fst"
                                     (Prims.of_int (74)) (Prims.of_int (34))
                                     (Prims.of_int (85)) (Prims.of_int (31)))))
                            (Obj.magic uu___2)
                            (fun uu___3 ->
                               (fun sc1 ->
                                  let uu___3 =
                                    FStar_Tactics_Util.map_opt
                                      (fun uu___4 ->
                                         match uu___4 with
                                         | (b, asc) ->
                                             let uu___5 =
                                               on_sort_binder (visit_tm ff) b in
                                             FStar_Tactics_Effect.tac_bind
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "FStar.Tactics.Visit.fst"
                                                        (Prims.of_int (76))
                                                        (Prims.of_int (18))
                                                        (Prims.of_int (76))
                                                        (Prims.of_int (48)))))
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "FStar.Tactics.Visit.fst"
                                                        (Prims.of_int (76))
                                                        (Prims.of_int (51))
                                                        (Prims.of_int (83))
                                                        (Prims.of_int (16)))))
                                               (Obj.magic uu___5)
                                               (fun uu___6 ->
                                                  (fun b1 ->
                                                     let uu___6 =
                                                       match asc with
                                                       | (FStar_Pervasives.Inl
                                                          t1, tacopt, use_eq)
                                                           ->
                                                           let uu___7 =
                                                             let uu___8 =
                                                               visit_tm ff t1 in
                                                             FStar_Tactics_Effect.tac_bind
                                                               (FStar_Sealed.seal
                                                                  (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Visit.fst"
                                                                    (Prims.of_int (80))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (80))
                                                                    (Prims.of_int (33)))))
                                                               (FStar_Sealed.seal
                                                                  (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Visit.fst"
                                                                    (Prims.of_int (80))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (80))
                                                                    (Prims.of_int (33)))))
                                                               (Obj.magic
                                                                  uu___8)
                                                               (fun uu___9 ->
                                                                  FStar_Tactics_Effect.lift_div_tac
                                                                    (
                                                                    fun
                                                                    uu___10
                                                                    ->
                                                                    FStar_Pervasives.Inl
                                                                    uu___9)) in
                                                           FStar_Tactics_Effect.tac_bind
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "FStar.Tactics.Visit.fst"
                                                                    (Prims.of_int (80))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (80))
                                                                    (Prims.of_int (33)))))
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "FStar.Tactics.Visit.fst"
                                                                    (Prims.of_int (80))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (80))
                                                                    (Prims.of_int (71)))))
                                                             (Obj.magic
                                                                uu___7)
                                                             (fun uu___8 ->
                                                                (fun uu___8
                                                                   ->
                                                                   let uu___9
                                                                    =
                                                                    FStar_Tactics_Util.map_opt
                                                                    (visit_tm
                                                                    ff)
                                                                    tacopt in
                                                                   Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Visit.fst"
                                                                    (Prims.of_int (80))
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (80))
                                                                    (Prims.of_int (63)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Visit.fst"
                                                                    (Prims.of_int (80))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (80))
                                                                    (Prims.of_int (71)))))
                                                                    (Obj.magic
                                                                    uu___9)
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    (uu___8,
                                                                    uu___10,
                                                                    use_eq)))))
                                                                  uu___8)
                                                       | (FStar_Pervasives.Inr
                                                          c, tacopt, use_eq)
                                                           ->
                                                           let uu___7 =
                                                             let uu___8 =
                                                               visit_comp ff
                                                                 c in
                                                             FStar_Tactics_Effect.tac_bind
                                                               (FStar_Sealed.seal
                                                                  (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Visit.fst"
                                                                    (Prims.of_int (82))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (82))
                                                                    (Prims.of_int (35)))))
                                                               (FStar_Sealed.seal
                                                                  (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Visit.fst"
                                                                    (Prims.of_int (82))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (82))
                                                                    (Prims.of_int (35)))))
                                                               (Obj.magic
                                                                  uu___8)
                                                               (fun uu___9 ->
                                                                  FStar_Tactics_Effect.lift_div_tac
                                                                    (
                                                                    fun
                                                                    uu___10
                                                                    ->
                                                                    FStar_Pervasives.Inr
                                                                    uu___9)) in
                                                           FStar_Tactics_Effect.tac_bind
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "FStar.Tactics.Visit.fst"
                                                                    (Prims.of_int (82))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (82))
                                                                    (Prims.of_int (35)))))
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "FStar.Tactics.Visit.fst"
                                                                    (Prims.of_int (82))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (82))
                                                                    (Prims.of_int (73)))))
                                                             (Obj.magic
                                                                uu___7)
                                                             (fun uu___8 ->
                                                                (fun uu___8
                                                                   ->
                                                                   let uu___9
                                                                    =
                                                                    FStar_Tactics_Util.map_opt
                                                                    (visit_tm
                                                                    ff)
                                                                    tacopt in
                                                                   Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Visit.fst"
                                                                    (Prims.of_int (82))
                                                                    (Prims.of_int (37))
                                                                    (Prims.of_int (82))
                                                                    (Prims.of_int (65)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Visit.fst"
                                                                    (Prims.of_int (82))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (82))
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
                                                                    (uu___8,
                                                                    uu___10,
                                                                    use_eq)))))
                                                                  uu___8) in
                                                     Obj.magic
                                                       (FStar_Tactics_Effect.tac_bind
                                                          (FStar_Sealed.seal
                                                             (Obj.magic
                                                                (FStar_Range.mk_range
                                                                   "FStar.Tactics.Visit.fst"
                                                                   (Prims.of_int (78))
                                                                   (Prims.of_int (12))
                                                                   (Prims.of_int (82))
                                                                   (Prims.of_int (73)))))
                                                          (FStar_Sealed.seal
                                                             (Obj.magic
                                                                (FStar_Range.mk_range
                                                                   "FStar.Tactics.Visit.fst"
                                                                   (Prims.of_int (83))
                                                                   (Prims.of_int (10))
                                                                   (Prims.of_int (83))
                                                                   (Prims.of_int (16)))))
                                                          (Obj.magic uu___6)
                                                          (fun asc1 ->
                                                             FStar_Tactics_Effect.lift_div_tac
                                                               (fun uu___7 ->
                                                                  (b1, asc1)))))
                                                    uu___6)) ret_opt in
                                  Obj.magic
                                    (FStar_Tactics_Effect.tac_bind
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "FStar.Tactics.Visit.fst"
                                                (Prims.of_int (75))
                                                (Prims.of_int (22))
                                                (Prims.of_int (83))
                                                (Prims.of_int (25)))))
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "FStar.Tactics.Visit.fst"
                                                (Prims.of_int (83))
                                                (Prims.of_int (28))
                                                (Prims.of_int (85))
                                                (Prims.of_int (31)))))
                                       (Obj.magic uu___3)
                                       (fun uu___4 ->
                                          (fun ret_opt1 ->
                                             let uu___4 =
                                               FStar_Tactics_Util.map
                                                 (visit_br ff) brs in
                                             Obj.magic
                                               (FStar_Tactics_Effect.tac_bind
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "FStar.Tactics.Visit.fst"
                                                           (Prims.of_int (84))
                                                           (Prims.of_int (18))
                                                           (Prims.of_int (84))
                                                           (Prims.of_int (39)))))
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "FStar.Tactics.Visit.fst"
                                                           (Prims.of_int (85))
                                                           (Prims.of_int (8))
                                                           (Prims.of_int (85))
                                                           (Prims.of_int (31)))))
                                                  (Obj.magic uu___4)
                                                  (fun brs1 ->
                                                     FStar_Tactics_Effect.lift_div_tac
                                                       (fun uu___5 ->
                                                          FStarC_Reflection_V2_Data.Tv_Match
                                                            (sc1, ret_opt1,
                                                              brs1)))))
                                            uu___4))) uu___3)))
                | FStarC_Reflection_V2_Data.Tv_AscribedT
                    (e, t1, topt, use_eq) ->
                    Obj.magic
                      (Obj.repr
                         (let uu___2 = visit_tm ff e in
                          FStar_Tactics_Effect.tac_bind
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.Visit.fst"
                                     (Prims.of_int (87)) (Prims.of_int (16))
                                     (Prims.of_int (87)) (Prims.of_int (29)))))
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.Visit.fst"
                                     (Prims.of_int (87)) (Prims.of_int (32))
                                     (Prims.of_int (89)) (Prims.of_int (36)))))
                            (Obj.magic uu___2)
                            (fun uu___3 ->
                               (fun e1 ->
                                  let uu___3 = visit_tm ff t1 in
                                  Obj.magic
                                    (FStar_Tactics_Effect.tac_bind
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "FStar.Tactics.Visit.fst"
                                                (Prims.of_int (88))
                                                (Prims.of_int (16))
                                                (Prims.of_int (88))
                                                (Prims.of_int (29)))))
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "FStar.Tactics.Visit.fst"
                                                (Prims.of_int (89))
                                                (Prims.of_int (8))
                                                (Prims.of_int (89))
                                                (Prims.of_int (36)))))
                                       (Obj.magic uu___3)
                                       (fun t2 ->
                                          FStar_Tactics_Effect.lift_div_tac
                                            (fun uu___4 ->
                                               FStarC_Reflection_V2_Data.Tv_AscribedT
                                                 (e1, t2, topt, use_eq)))))
                                 uu___3)))
                | FStarC_Reflection_V2_Data.Tv_AscribedC (e, c, topt, use_eq)
                    ->
                    Obj.magic
                      (Obj.repr
                         (let uu___2 = visit_tm ff e in
                          FStar_Tactics_Effect.tac_bind
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.Visit.fst"
                                     (Prims.of_int (91)) (Prims.of_int (16))
                                     (Prims.of_int (91)) (Prims.of_int (29)))))
                            (FStar_Sealed.seal
                               (Obj.magic
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.Visit.fst"
                                     (Prims.of_int (91)) (Prims.of_int (32))
                                     (Prims.of_int (93)) (Prims.of_int (36)))))
                            (Obj.magic uu___2)
                            (fun uu___3 ->
                               (fun e1 ->
                                  let uu___3 = visit_comp ff c in
                                  Obj.magic
                                    (FStar_Tactics_Effect.tac_bind
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "FStar.Tactics.Visit.fst"
                                                (Prims.of_int (92))
                                                (Prims.of_int (16))
                                                (Prims.of_int (92))
                                                (Prims.of_int (31)))))
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "FStar.Tactics.Visit.fst"
                                                (Prims.of_int (93))
                                                (Prims.of_int (8))
                                                (Prims.of_int (93))
                                                (Prims.of_int (36)))))
                                       (Obj.magic uu___3)
                                       (fun c1 ->
                                          FStar_Tactics_Effect.lift_div_tac
                                            (fun uu___4 ->
                                               FStarC_Reflection_V2_Data.Tv_AscribedC
                                                 (e1, c1, topt, use_eq)))))
                                 uu___3))) in
              Obj.magic
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "FStar.Tactics.Visit.fst"
                            (Prims.of_int (41)) (Prims.of_int (4))
                            (Prims.of_int (93)) (Prims.of_int (36)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "FStar.Tactics.Visit.fst"
                            (Prims.of_int (95)) (Prims.of_int (2))
                            (Prims.of_int (95)) (Prims.of_int (18)))))
                   (Obj.magic uu___1)
                   (fun uu___2 ->
                      (fun tv' ->
                         Obj.magic
                           (ff (FStarC_Reflection_V2_Builtins.pack_ln tv')))
                        uu___2))) uu___1)
and (visit_br :
  (FStarC_Reflection_Types.term ->
     (FStarC_Reflection_Types.term, unit) FStar_Tactics_Effect.tac_repr)
    ->
    FStarC_Reflection_V2_Data.branch ->
      (FStarC_Reflection_V2_Data.branch, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun ff ->
    fun b ->
      let uu___ =
        Obj.magic (FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> b)) in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.Visit.fst"
                 (Prims.of_int (97)) (Prims.of_int (15)) (Prims.of_int (97))
                 (Prims.of_int (16)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.Visit.fst"
                 (Prims.of_int (96)) (Prims.of_int (62)) (Prims.of_int (100))
                 (Prims.of_int (8))))) (Obj.magic uu___)
        (fun uu___1 ->
           (fun uu___1 ->
              match uu___1 with
              | (p, t) ->
                  let uu___2 = visit_pat ff p in
                  Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "FStar.Tactics.Visit.fst"
                                (Prims.of_int (98)) (Prims.of_int (10))
                                (Prims.of_int (98)) (Prims.of_int (24)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "FStar.Tactics.Visit.fst"
                                (Prims.of_int (98)) (Prims.of_int (27))
                                (Prims.of_int (100)) (Prims.of_int (8)))))
                       (Obj.magic uu___2)
                       (fun uu___3 ->
                          (fun p1 ->
                             let uu___3 = visit_tm ff t in
                             Obj.magic
                               (FStar_Tactics_Effect.tac_bind
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "FStar.Tactics.Visit.fst"
                                           (Prims.of_int (99))
                                           (Prims.of_int (10))
                                           (Prims.of_int (99))
                                           (Prims.of_int (23)))))
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "FStar.Tactics.Visit.fst"
                                           (Prims.of_int (100))
                                           (Prims.of_int (2))
                                           (Prims.of_int (100))
                                           (Prims.of_int (8)))))
                                  (Obj.magic uu___3)
                                  (fun t1 ->
                                     FStar_Tactics_Effect.lift_div_tac
                                       (fun uu___4 -> (p1, t1))))) uu___3)))
             uu___1)
and (visit_pat :
  (FStarC_Reflection_Types.term ->
     (FStarC_Reflection_Types.term, unit) FStar_Tactics_Effect.tac_repr)
    ->
    FStarC_Reflection_V2_Data.pattern ->
      (FStarC_Reflection_V2_Data.pattern, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun ff ->
         fun p ->
           match p with
           | FStarC_Reflection_V2_Data.Pat_Constant uu___ ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> p)))
           | FStarC_Reflection_V2_Data.Pat_Var (v, s) ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.lift_div_tac
                       (fun uu___ -> FStarC_Reflection_V2_Data.Pat_Var (v, s))))
           | FStarC_Reflection_V2_Data.Pat_Cons (head, univs, subpats) ->
               Obj.magic
                 (Obj.repr
                    (let uu___ =
                       FStar_Tactics_Util.map
                         (fun uu___1 ->
                            match uu___1 with
                            | (p1, b) ->
                                let uu___2 = visit_pat ff p1 in
                                FStar_Tactics_Effect.tac_bind
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "FStar.Tactics.Visit.fst"
                                           (Prims.of_int (106))
                                           (Prims.of_int (39))
                                           (Prims.of_int (106))
                                           (Prims.of_int (53)))))
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "FStar.Tactics.Visit.fst"
                                           (Prims.of_int (106))
                                           (Prims.of_int (38))
                                           (Prims.of_int (106))
                                           (Prims.of_int (57)))))
                                  (Obj.magic uu___2)
                                  (fun uu___3 ->
                                     FStar_Tactics_Effect.lift_div_tac
                                       (fun uu___4 -> (uu___3, b)))) subpats in
                     FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "FStar.Tactics.Visit.fst"
                                (Prims.of_int (106)) (Prims.of_int (20))
                                (Prims.of_int (106)) (Prims.of_int (67)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "FStar.Tactics.Visit.fst"
                                (Prims.of_int (107)) (Prims.of_int (6))
                                (Prims.of_int (107)) (Prims.of_int (33)))))
                       (Obj.magic uu___)
                       (fun subpats1 ->
                          FStar_Tactics_Effect.lift_div_tac
                            (fun uu___1 ->
                               FStarC_Reflection_V2_Data.Pat_Cons
                                 (head, univs, subpats1)))))
           | FStarC_Reflection_V2_Data.Pat_Dot_Term t ->
               Obj.magic
                 (Obj.repr
                    (let uu___ = FStar_Tactics_Util.map_opt (visit_tm ff) t in
                     FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "FStar.Tactics.Visit.fst"
                                (Prims.of_int (109)) (Prims.of_int (14))
                                (Prims.of_int (109)) (Prims.of_int (37)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range "FStar.Tactics.Visit.fst"
                                (Prims.of_int (110)) (Prims.of_int (6))
                                (Prims.of_int (110)) (Prims.of_int (20)))))
                       (Obj.magic uu___)
                       (fun t1 ->
                          FStar_Tactics_Effect.lift_div_tac
                            (fun uu___1 ->
                               FStarC_Reflection_V2_Data.Pat_Dot_Term t1)))))
        uu___1 uu___
and (visit_comp :
  (FStarC_Reflection_Types.term ->
     (FStarC_Reflection_Types.term, unit) FStar_Tactics_Effect.tac_repr)
    ->
    FStarC_Reflection_Types.comp ->
      (FStarC_Reflection_Types.comp, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun ff ->
    fun c ->
      let uu___ =
        Obj.magic
          (FStar_Tactics_Effect.lift_div_tac
             (fun uu___1 -> FStarC_Reflection_V2_Builtins.inspect_comp c)) in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.Visit.fst"
                 (Prims.of_int (113)) (Prims.of_int (11))
                 (Prims.of_int (113)) (Prims.of_int (25)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.Visit.fst"
                 (Prims.of_int (113)) (Prims.of_int (28))
                 (Prims.of_int (136)) (Prims.of_int (15)))))
        (Obj.magic uu___)
        (fun uu___1 ->
           (fun cv ->
              let uu___1 =
                match cv with
                | FStarC_Reflection_V2_Data.C_Total ret ->
                    let uu___2 = visit_tm ff ret in
                    FStar_Tactics_Effect.tac_bind
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range "FStar.Tactics.Visit.fst"
                               (Prims.of_int (117)) (Prims.of_int (18))
                               (Prims.of_int (117)) (Prims.of_int (33)))))
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range "FStar.Tactics.Visit.fst"
                               (Prims.of_int (118)) (Prims.of_int (8))
                               (Prims.of_int (118)) (Prims.of_int (19)))))
                      (Obj.magic uu___2)
                      (fun ret1 ->
                         FStar_Tactics_Effect.lift_div_tac
                           (fun uu___3 ->
                              FStarC_Reflection_V2_Data.C_Total ret1))
                | FStarC_Reflection_V2_Data.C_GTotal ret ->
                    let uu___2 = visit_tm ff ret in
                    FStar_Tactics_Effect.tac_bind
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range "FStar.Tactics.Visit.fst"
                               (Prims.of_int (121)) (Prims.of_int (18))
                               (Prims.of_int (121)) (Prims.of_int (33)))))
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range "FStar.Tactics.Visit.fst"
                               (Prims.of_int (122)) (Prims.of_int (8))
                               (Prims.of_int (122)) (Prims.of_int (20)))))
                      (Obj.magic uu___2)
                      (fun ret1 ->
                         FStar_Tactics_Effect.lift_div_tac
                           (fun uu___3 ->
                              FStarC_Reflection_V2_Data.C_GTotal ret1))
                | FStarC_Reflection_V2_Data.C_Lemma (pre, post, pats) ->
                    let uu___2 = visit_tm ff pre in
                    FStar_Tactics_Effect.tac_bind
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range "FStar.Tactics.Visit.fst"
                               (Prims.of_int (125)) (Prims.of_int (18))
                               (Prims.of_int (125)) (Prims.of_int (33)))))
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range "FStar.Tactics.Visit.fst"
                               (Prims.of_int (125)) (Prims.of_int (36))
                               (Prims.of_int (128)) (Prims.of_int (29)))))
                      (Obj.magic uu___2)
                      (fun uu___3 ->
                         (fun pre1 ->
                            let uu___3 = visit_tm ff post in
                            Obj.magic
                              (FStar_Tactics_Effect.tac_bind
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "FStar.Tactics.Visit.fst"
                                          (Prims.of_int (126))
                                          (Prims.of_int (19))
                                          (Prims.of_int (126))
                                          (Prims.of_int (35)))))
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "FStar.Tactics.Visit.fst"
                                          (Prims.of_int (126))
                                          (Prims.of_int (38))
                                          (Prims.of_int (128))
                                          (Prims.of_int (29)))))
                                 (Obj.magic uu___3)
                                 (fun uu___4 ->
                                    (fun post1 ->
                                       let uu___4 = visit_tm ff pats in
                                       Obj.magic
                                         (FStar_Tactics_Effect.tac_bind
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "FStar.Tactics.Visit.fst"
                                                     (Prims.of_int (127))
                                                     (Prims.of_int (19))
                                                     (Prims.of_int (127))
                                                     (Prims.of_int (35)))))
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "FStar.Tactics.Visit.fst"
                                                     (Prims.of_int (128))
                                                     (Prims.of_int (8))
                                                     (Prims.of_int (128))
                                                     (Prims.of_int (29)))))
                                            (Obj.magic uu___4)
                                            (fun pats1 ->
                                               FStar_Tactics_Effect.lift_div_tac
                                                 (fun uu___5 ->
                                                    FStarC_Reflection_V2_Data.C_Lemma
                                                      (pre1, post1, pats1)))))
                                      uu___4))) uu___3)
                | FStarC_Reflection_V2_Data.C_Eff (us, eff, res, args, decrs)
                    ->
                    let uu___2 = visit_tm ff res in
                    FStar_Tactics_Effect.tac_bind
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range "FStar.Tactics.Visit.fst"
                               (Prims.of_int (131)) (Prims.of_int (18))
                               (Prims.of_int (131)) (Prims.of_int (33)))))
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range "FStar.Tactics.Visit.fst"
                               (Prims.of_int (131)) (Prims.of_int (36))
                               (Prims.of_int (134)) (Prims.of_int (35)))))
                      (Obj.magic uu___2)
                      (fun uu___3 ->
                         (fun res1 ->
                            let uu___3 =
                              FStar_Tactics_Util.map
                                (fun uu___4 ->
                                   match uu___4 with
                                   | (a, q) ->
                                       let uu___5 = visit_tm ff a in
                                       FStar_Tactics_Effect.tac_bind
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "FStar.Tactics.Visit.fst"
                                                  (Prims.of_int (132))
                                                  (Prims.of_int (39))
                                                  (Prims.of_int (132))
                                                  (Prims.of_int (52)))))
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "FStar.Tactics.Visit.fst"
                                                  (Prims.of_int (132))
                                                  (Prims.of_int (38))
                                                  (Prims.of_int (132))
                                                  (Prims.of_int (56)))))
                                         (Obj.magic uu___5)
                                         (fun uu___6 ->
                                            FStar_Tactics_Effect.lift_div_tac
                                              (fun uu___7 -> (uu___6, q))))
                                args in
                            Obj.magic
                              (FStar_Tactics_Effect.tac_bind
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "FStar.Tactics.Visit.fst"
                                          (Prims.of_int (132))
                                          (Prims.of_int (19))
                                          (Prims.of_int (132))
                                          (Prims.of_int (62)))))
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "FStar.Tactics.Visit.fst"
                                          (Prims.of_int (132))
                                          (Prims.of_int (65))
                                          (Prims.of_int (134))
                                          (Prims.of_int (35)))))
                                 (Obj.magic uu___3)
                                 (fun uu___4 ->
                                    (fun args1 ->
                                       let uu___4 =
                                         FStar_Tactics_Util.map (visit_tm ff)
                                           decrs in
                                       Obj.magic
                                         (FStar_Tactics_Effect.tac_bind
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "FStar.Tactics.Visit.fst"
                                                     (Prims.of_int (133))
                                                     (Prims.of_int (20))
                                                     (Prims.of_int (133))
                                                     (Prims.of_int (43)))))
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "FStar.Tactics.Visit.fst"
                                                     (Prims.of_int (134))
                                                     (Prims.of_int (8))
                                                     (Prims.of_int (134))
                                                     (Prims.of_int (35)))))
                                            (Obj.magic uu___4)
                                            (fun decrs1 ->
                                               FStar_Tactics_Effect.lift_div_tac
                                                 (fun uu___5 ->
                                                    FStarC_Reflection_V2_Data.C_Eff
                                                      (us, eff, res1, args1,
                                                        decrs1))))) uu___4)))
                           uu___3) in
              Obj.magic
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "FStar.Tactics.Visit.fst"
                            (Prims.of_int (115)) (Prims.of_int (4))
                            (Prims.of_int (134)) (Prims.of_int (35)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "FStar.Tactics.Visit.fst"
                            (Prims.of_int (136)) (Prims.of_int (2))
                            (Prims.of_int (136)) (Prims.of_int (15)))))
                   (Obj.magic uu___1)
                   (fun cv' ->
                      FStar_Tactics_Effect.lift_div_tac
                        (fun uu___2 ->
                           FStarC_Reflection_V2_Builtins.pack_comp cv'))))
             uu___1)