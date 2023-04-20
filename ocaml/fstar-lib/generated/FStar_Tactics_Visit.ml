open Prims
let (on_sort_bv :
  (FStar_Reflection_Types.term ->
     (FStar_Reflection_Types.term, unit) FStar_Tactics_Effect.tac_repr)
    ->
    FStar_Reflection_Types.bv ->
      (FStar_Reflection_Types.bv, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun f ->
    fun xbv ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Range.mk_range "FStar.Tactics.Visit.fst" (Prims.of_int (26))
           (Prims.of_int (12)) (Prims.of_int (26)) (Prims.of_int (26)))
        (FStar_Range.mk_range "FStar.Tactics.Visit.fst" (Prims.of_int (27))
           (Prims.of_int (2)) (Prims.of_int (29)) (Prims.of_int (4)))
        (FStar_Tactics_Effect.lift_div_tac
           (fun uu___ -> FStar_Reflection_Builtins.inspect_bv xbv))
        (fun uu___ ->
           (fun bvv ->
              Obj.magic
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Range.mk_range "FStar.Tactics.Visit.fst"
                      (Prims.of_int (27)) (Prims.of_int (14))
                      (Prims.of_int (27)) (Prims.of_int (46)))
                   (FStar_Range.mk_range "FStar.Tactics.Visit.fst"
                      (Prims.of_int (28)) (Prims.of_int (11))
                      (Prims.of_int (28)) (Prims.of_int (22)))
                   (Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (FStar_Range.mk_range "FStar.Tactics.Visit.fst"
                            (Prims.of_int (27)) (Prims.of_int (33))
                            (Prims.of_int (27)) (Prims.of_int (46)))
                         (FStar_Range.mk_range "FStar.Tactics.Visit.fst"
                            (Prims.of_int (27)) (Prims.of_int (14))
                            (Prims.of_int (27)) (Prims.of_int (46)))
                         (Obj.magic (f bvv.FStar_Reflection_Data.bv_sort))
                         (fun uu___ ->
                            FStar_Tactics_Effect.lift_div_tac
                              (fun uu___1 ->
                                 {
                                   FStar_Reflection_Data.bv_ppname =
                                     (bvv.FStar_Reflection_Data.bv_ppname);
                                   FStar_Reflection_Data.bv_index =
                                     (bvv.FStar_Reflection_Data.bv_index);
                                   FStar_Reflection_Data.bv_sort = uu___
                                 }))))
                   (fun bvv1 ->
                      FStar_Tactics_Effect.lift_div_tac
                        (fun uu___ -> FStar_Reflection_Builtins.pack_bv bvv1))))
             uu___)
let (on_sort_binder :
  (FStar_Reflection_Types.term ->
     (FStar_Reflection_Types.term, unit) FStar_Tactics_Effect.tac_repr)
    ->
    FStar_Reflection_Types.binder ->
      (FStar_Reflection_Types.binder, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun f ->
    fun b ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Range.mk_range "FStar.Tactics.Visit.fst" (Prims.of_int (32))
           (Prims.of_int (14)) (Prims.of_int (32)) (Prims.of_int (30)))
        (FStar_Range.mk_range "FStar.Tactics.Visit.fst" (Prims.of_int (33))
           (Prims.of_int (2)) (Prims.of_int (34)) (Prims.of_int (39)))
        (FStar_Tactics_Effect.lift_div_tac
           (fun uu___ -> FStar_Reflection_Builtins.inspect_binder b))
        (fun uu___ ->
           (fun bview ->
              Obj.magic
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Range.mk_range "FStar.Tactics.Visit.fst"
                      (Prims.of_int (33)) (Prims.of_int (11))
                      (Prims.of_int (33)) (Prims.of_int (39)))
                   (FStar_Range.mk_range "FStar.Tactics.Visit.fst"
                      (Prims.of_int (34)) (Prims.of_int (2))
                      (Prims.of_int (34)) (Prims.of_int (39)))
                   (Obj.magic
                      (on_sort_bv f bview.FStar_Reflection_Data.binder_bv))
                   (fun bv ->
                      FStar_Tactics_Effect.lift_div_tac
                        (fun uu___ ->
                           FStar_Reflection_Builtins.pack_binder
                             {
                               FStar_Reflection_Data.binder_bv = bv;
                               FStar_Reflection_Data.binder_qual =
                                 (bview.FStar_Reflection_Data.binder_qual);
                               FStar_Reflection_Data.binder_attrs =
                                 (bview.FStar_Reflection_Data.binder_attrs)
                             })))) uu___)
let rec (visit_tm :
  (FStar_Reflection_Types.term ->
     (FStar_Reflection_Types.term, unit) FStar_Tactics_Effect.tac_repr)
    ->
    FStar_Reflection_Types.term ->
      (FStar_Reflection_Types.term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun ff ->
    fun t ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Range.mk_range "FStar.Tactics.Visit.fst" (Prims.of_int (37))
           (Prims.of_int (11)) (Prims.of_int (37)) (Prims.of_int (23)))
        (FStar_Range.mk_range "FStar.Tactics.Visit.fst" (Prims.of_int (38))
           (Prims.of_int (2)) (Prims.of_int (96)) (Prims.of_int (18)))
        (FStar_Tactics_Effect.lift_div_tac
           (fun uu___ -> FStar_Reflection_Builtins.inspect_ln t))
        (fun uu___ ->
           (fun tv ->
              Obj.magic
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Range.mk_range "FStar.Tactics.Visit.fst"
                      (Prims.of_int (39)) (Prims.of_int (4))
                      (Prims.of_int (94)) (Prims.of_int (36)))
                   (FStar_Range.mk_range "FStar.Tactics.Visit.fst"
                      (Prims.of_int (96)) (Prims.of_int (2))
                      (Prims.of_int (96)) (Prims.of_int (18)))
                   (match tv with
                    | FStar_Reflection_Data.Tv_FVar uu___ ->
                        Obj.magic
                          (Obj.repr
                             (FStar_Tactics_Effect.lift_div_tac
                                (fun uu___1 -> tv)))
                    | FStar_Reflection_Data.Tv_UInst (uu___, uu___1) ->
                        Obj.magic
                          (Obj.repr
                             (FStar_Tactics_Effect.lift_div_tac
                                (fun uu___2 -> tv)))
                    | FStar_Reflection_Data.Tv_Var bv ->
                        Obj.magic
                          (Obj.repr
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Range.mk_range
                                   "FStar.Tactics.Visit.fst"
                                   (Prims.of_int (43)) (Prims.of_int (17))
                                   (Prims.of_int (43)) (Prims.of_int (44)))
                                (FStar_Range.mk_range
                                   "FStar.Tactics.Visit.fst"
                                   (Prims.of_int (44)) (Prims.of_int (8))
                                   (Prims.of_int (44)) (Prims.of_int (17)))
                                (Obj.magic (on_sort_bv (visit_tm ff) bv))
                                (fun bv1 ->
                                   FStar_Tactics_Effect.lift_div_tac
                                     (fun uu___ ->
                                        FStar_Reflection_Data.Tv_Var bv1))))
                    | FStar_Reflection_Data.Tv_BVar bv ->
                        Obj.magic
                          (Obj.repr
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Range.mk_range
                                   "FStar.Tactics.Visit.fst"
                                   (Prims.of_int (47)) (Prims.of_int (17))
                                   (Prims.of_int (47)) (Prims.of_int (44)))
                                (FStar_Range.mk_range
                                   "FStar.Tactics.Visit.fst"
                                   (Prims.of_int (48)) (Prims.of_int (8))
                                   (Prims.of_int (48)) (Prims.of_int (18)))
                                (Obj.magic (on_sort_bv (visit_tm ff) bv))
                                (fun bv1 ->
                                   FStar_Tactics_Effect.lift_div_tac
                                     (fun uu___ ->
                                        FStar_Reflection_Data.Tv_BVar bv1))))
                    | FStar_Reflection_Data.Tv_Type u ->
                        Obj.magic
                          (Obj.repr
                             (FStar_Tactics_Effect.lift_div_tac
                                (fun uu___ -> FStar_Reflection_Data.Tv_Type u)))
                    | FStar_Reflection_Data.Tv_Const c ->
                        Obj.magic
                          (Obj.repr
                             (FStar_Tactics_Effect.lift_div_tac
                                (fun uu___ ->
                                   FStar_Reflection_Data.Tv_Const c)))
                    | FStar_Reflection_Data.Tv_Uvar (i, u) ->
                        Obj.magic
                          (Obj.repr
                             (FStar_Tactics_Effect.lift_div_tac
                                (fun uu___ ->
                                   FStar_Reflection_Data.Tv_Uvar (i, u))))
                    | FStar_Reflection_Data.Tv_Unknown ->
                        Obj.magic
                          (Obj.repr
                             (FStar_Tactics_Effect.lift_div_tac
                                (fun uu___ ->
                                   FStar_Reflection_Data.Tv_Unknown)))
                    | FStar_Reflection_Data.Tv_Arrow (b, c) ->
                        Obj.magic
                          (Obj.repr
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Range.mk_range
                                   "FStar.Tactics.Visit.fst"
                                   (Prims.of_int (55)) (Prims.of_int (16))
                                   (Prims.of_int (55)) (Prims.of_int (46)))
                                (FStar_Range.mk_range
                                   "FStar.Tactics.Visit.fst"
                                   (Prims.of_int (56)) (Prims.of_int (8))
                                   (Prims.of_int (57)) (Prims.of_int (20)))
                                (Obj.magic (on_sort_binder (visit_tm ff) b))
                                (fun uu___ ->
                                   (fun b1 ->
                                      Obj.magic
                                        (FStar_Tactics_Effect.tac_bind
                                           (FStar_Range.mk_range
                                              "FStar.Tactics.Visit.fst"
                                              (Prims.of_int (56))
                                              (Prims.of_int (16))
                                              (Prims.of_int (56))
                                              (Prims.of_int (31)))
                                           (FStar_Range.mk_range
                                              "FStar.Tactics.Visit.fst"
                                              (Prims.of_int (57))
                                              (Prims.of_int (8))
                                              (Prims.of_int (57))
                                              (Prims.of_int (20)))
                                           (Obj.magic (visit_comp ff c))
                                           (fun c1 ->
                                              FStar_Tactics_Effect.lift_div_tac
                                                (fun uu___ ->
                                                   FStar_Reflection_Data.Tv_Arrow
                                                     (b1, c1))))) uu___)))
                    | FStar_Reflection_Data.Tv_Abs (b, t1) ->
                        Obj.magic
                          (Obj.repr
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Range.mk_range
                                   "FStar.Tactics.Visit.fst"
                                   (Prims.of_int (59)) (Prims.of_int (16))
                                   (Prims.of_int (59)) (Prims.of_int (46)))
                                (FStar_Range.mk_range
                                   "FStar.Tactics.Visit.fst"
                                   (Prims.of_int (60)) (Prims.of_int (8))
                                   (Prims.of_int (61)) (Prims.of_int (18)))
                                (Obj.magic (on_sort_binder (visit_tm ff) b))
                                (fun uu___ ->
                                   (fun b1 ->
                                      Obj.magic
                                        (FStar_Tactics_Effect.tac_bind
                                           (FStar_Range.mk_range
                                              "FStar.Tactics.Visit.fst"
                                              (Prims.of_int (60))
                                              (Prims.of_int (16))
                                              (Prims.of_int (60))
                                              (Prims.of_int (29)))
                                           (FStar_Range.mk_range
                                              "FStar.Tactics.Visit.fst"
                                              (Prims.of_int (61))
                                              (Prims.of_int (8))
                                              (Prims.of_int (61))
                                              (Prims.of_int (18)))
                                           (Obj.magic (visit_tm ff t1))
                                           (fun t2 ->
                                              FStar_Tactics_Effect.lift_div_tac
                                                (fun uu___ ->
                                                   FStar_Reflection_Data.Tv_Abs
                                                     (b1, t2))))) uu___)))
                    | FStar_Reflection_Data.Tv_App (l, (r, q)) ->
                        Obj.magic
                          (Obj.repr
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Range.mk_range
                                   "FStar.Tactics.Visit.fst"
                                   (Prims.of_int (63)) (Prims.of_int (17))
                                   (Prims.of_int (63)) (Prims.of_int (30)))
                                (FStar_Range.mk_range
                                   "FStar.Tactics.Visit.fst"
                                   (Prims.of_int (64)) (Prims.of_int (9))
                                   (Prims.of_int (65)) (Prims.of_int (24)))
                                (Obj.magic (visit_tm ff l))
                                (fun uu___ ->
                                   (fun l1 ->
                                      Obj.magic
                                        (FStar_Tactics_Effect.tac_bind
                                           (FStar_Range.mk_range
                                              "FStar.Tactics.Visit.fst"
                                              (Prims.of_int (64))
                                              (Prims.of_int (17))
                                              (Prims.of_int (64))
                                              (Prims.of_int (30)))
                                           (FStar_Range.mk_range
                                              "FStar.Tactics.Visit.fst"
                                              (Prims.of_int (65))
                                              (Prims.of_int (9))
                                              (Prims.of_int (65))
                                              (Prims.of_int (24)))
                                           (Obj.magic (visit_tm ff r))
                                           (fun r1 ->
                                              FStar_Tactics_Effect.lift_div_tac
                                                (fun uu___ ->
                                                   FStar_Reflection_Data.Tv_App
                                                     (l1, (r1, q)))))) uu___)))
                    | FStar_Reflection_Data.Tv_Refine (b, r) ->
                        Obj.magic
                          (Obj.repr
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Range.mk_range
                                   "FStar.Tactics.Visit.fst"
                                   (Prims.of_int (67)) (Prims.of_int (16))
                                   (Prims.of_int (67)) (Prims.of_int (42)))
                                (FStar_Range.mk_range
                                   "FStar.Tactics.Visit.fst"
                                   (Prims.of_int (68)) (Prims.of_int (8))
                                   (Prims.of_int (69)) (Prims.of_int (21)))
                                (Obj.magic (on_sort_bv (visit_tm ff) b))
                                (fun uu___ ->
                                   (fun b1 ->
                                      Obj.magic
                                        (FStar_Tactics_Effect.tac_bind
                                           (FStar_Range.mk_range
                                              "FStar.Tactics.Visit.fst"
                                              (Prims.of_int (68))
                                              (Prims.of_int (16))
                                              (Prims.of_int (68))
                                              (Prims.of_int (29)))
                                           (FStar_Range.mk_range
                                              "FStar.Tactics.Visit.fst"
                                              (Prims.of_int (69))
                                              (Prims.of_int (8))
                                              (Prims.of_int (69))
                                              (Prims.of_int (21)))
                                           (Obj.magic (visit_tm ff r))
                                           (fun r1 ->
                                              FStar_Tactics_Effect.lift_div_tac
                                                (fun uu___ ->
                                                   FStar_Reflection_Data.Tv_Refine
                                                     (b1, r1))))) uu___)))
                    | FStar_Reflection_Data.Tv_Let (r, attrs, b, def, t1) ->
                        Obj.magic
                          (Obj.repr
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Range.mk_range
                                   "FStar.Tactics.Visit.fst"
                                   (Prims.of_int (71)) (Prims.of_int (16))
                                   (Prims.of_int (71)) (Prims.of_int (42)))
                                (FStar_Range.mk_range
                                   "FStar.Tactics.Visit.fst"
                                   (Prims.of_int (72)) (Prims.of_int (8))
                                   (Prims.of_int (74)) (Prims.of_int (30)))
                                (Obj.magic (on_sort_bv (visit_tm ff) b))
                                (fun uu___ ->
                                   (fun b1 ->
                                      Obj.magic
                                        (FStar_Tactics_Effect.tac_bind
                                           (FStar_Range.mk_range
                                              "FStar.Tactics.Visit.fst"
                                              (Prims.of_int (72))
                                              (Prims.of_int (18))
                                              (Prims.of_int (72))
                                              (Prims.of_int (33)))
                                           (FStar_Range.mk_range
                                              "FStar.Tactics.Visit.fst"
                                              (Prims.of_int (73))
                                              (Prims.of_int (8))
                                              (Prims.of_int (74))
                                              (Prims.of_int (30)))
                                           (Obj.magic (visit_tm ff def))
                                           (fun uu___ ->
                                              (fun def1 ->
                                                 Obj.magic
                                                   (FStar_Tactics_Effect.tac_bind
                                                      (FStar_Range.mk_range
                                                         "FStar.Tactics.Visit.fst"
                                                         (Prims.of_int (73))
                                                         (Prims.of_int (16))
                                                         (Prims.of_int (73))
                                                         (Prims.of_int (29)))
                                                      (FStar_Range.mk_range
                                                         "FStar.Tactics.Visit.fst"
                                                         (Prims.of_int (74))
                                                         (Prims.of_int (8))
                                                         (Prims.of_int (74))
                                                         (Prims.of_int (30)))
                                                      (Obj.magic
                                                         (visit_tm ff t1))
                                                      (fun t2 ->
                                                         FStar_Tactics_Effect.lift_div_tac
                                                           (fun uu___ ->
                                                              FStar_Reflection_Data.Tv_Let
                                                                (r, attrs,
                                                                  b1, def1,
                                                                  t2)))))
                                                uu___))) uu___)))
                    | FStar_Reflection_Data.Tv_Match (sc, ret_opt, brs) ->
                        Obj.magic
                          (Obj.repr
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Range.mk_range
                                   "FStar.Tactics.Visit.fst"
                                   (Prims.of_int (76)) (Prims.of_int (17))
                                   (Prims.of_int (76)) (Prims.of_int (31)))
                                (FStar_Range.mk_range
                                   "FStar.Tactics.Visit.fst"
                                   (Prims.of_int (77)) (Prims.of_int (8))
                                   (Prims.of_int (87)) (Prims.of_int (31)))
                                (Obj.magic (visit_tm ff sc))
                                (fun uu___ ->
                                   (fun sc1 ->
                                      Obj.magic
                                        (FStar_Tactics_Effect.tac_bind
                                           (FStar_Range.mk_range
                                              "FStar.Tactics.Visit.fst"
                                              (Prims.of_int (77))
                                              (Prims.of_int (22))
                                              (Prims.of_int (85))
                                              (Prims.of_int (25)))
                                           (FStar_Range.mk_range
                                              "FStar.Tactics.Visit.fst"
                                              (Prims.of_int (86))
                                              (Prims.of_int (8))
                                              (Prims.of_int (87))
                                              (Prims.of_int (31)))
                                           (Obj.magic
                                              (FStar_Tactics_Util.map_opt
                                                 (fun uu___ ->
                                                    match uu___ with
                                                    | (b, asc) ->
                                                        FStar_Tactics_Effect.tac_bind
                                                          (FStar_Range.mk_range
                                                             "FStar.Tactics.Visit.fst"
                                                             (Prims.of_int (78))
                                                             (Prims.of_int (18))
                                                             (Prims.of_int (78))
                                                             (Prims.of_int (48)))
                                                          (FStar_Range.mk_range
                                                             "FStar.Tactics.Visit.fst"
                                                             (Prims.of_int (79))
                                                             (Prims.of_int (10))
                                                             (Prims.of_int (85))
                                                             (Prims.of_int (16)))
                                                          (Obj.magic
                                                             (on_sort_binder
                                                                (visit_tm ff)
                                                                b))
                                                          (fun uu___1 ->
                                                             (fun b1 ->
                                                                Obj.magic
                                                                  (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Visit.fst"
                                                                    (Prims.of_int (80))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (84))
                                                                    (Prims.of_int (73)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Visit.fst"
                                                                    (Prims.of_int (85))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (85))
                                                                    (Prims.of_int (16)))
                                                                    (match asc
                                                                    with
                                                                    | 
                                                                    (FStar_Pervasives.Inl
                                                                    t1,
                                                                    tacopt,
                                                                    use_eq)
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Visit.fst"
                                                                    (Prims.of_int (82))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (82))
                                                                    (Prims.of_int (33)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Visit.fst"
                                                                    (Prims.of_int (82))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (82))
                                                                    (Prims.of_int (71)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Visit.fst"
                                                                    (Prims.of_int (82))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (82))
                                                                    (Prims.of_int (33)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Visit.fst"
                                                                    (Prims.of_int (82))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (82))
                                                                    (Prims.of_int (33)))
                                                                    (Obj.magic
                                                                    (visit_tm
                                                                    ff t1))
                                                                    (fun
                                                                    uu___1 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Pervasives.Inl
                                                                    uu___1))))
                                                                    (fun
                                                                    uu___1 ->
                                                                    (fun
                                                                    uu___1 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Visit.fst"
                                                                    (Prims.of_int (82))
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (82))
                                                                    (Prims.of_int (63)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Visit.fst"
                                                                    (Prims.of_int (82))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (82))
                                                                    (Prims.of_int (71)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Util.map_opt
                                                                    (visit_tm
                                                                    ff)
                                                                    tacopt))
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    (uu___1,
                                                                    uu___2,
                                                                    use_eq)))))
                                                                    uu___1))
                                                                    | 
                                                                    (FStar_Pervasives.Inr
                                                                    c,
                                                                    tacopt,
                                                                    use_eq)
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Visit.fst"
                                                                    (Prims.of_int (84))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (84))
                                                                    (Prims.of_int (35)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Visit.fst"
                                                                    (Prims.of_int (84))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (84))
                                                                    (Prims.of_int (73)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Visit.fst"
                                                                    (Prims.of_int (84))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (84))
                                                                    (Prims.of_int (35)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Visit.fst"
                                                                    (Prims.of_int (84))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (84))
                                                                    (Prims.of_int (35)))
                                                                    (Obj.magic
                                                                    (visit_comp
                                                                    ff c))
                                                                    (fun
                                                                    uu___1 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Pervasives.Inr
                                                                    uu___1))))
                                                                    (fun
                                                                    uu___1 ->
                                                                    (fun
                                                                    uu___1 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Visit.fst"
                                                                    (Prims.of_int (84))
                                                                    (Prims.of_int (37))
                                                                    (Prims.of_int (84))
                                                                    (Prims.of_int (65)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.Visit.fst"
                                                                    (Prims.of_int (84))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (84))
                                                                    (Prims.of_int (73)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Util.map_opt
                                                                    (visit_tm
                                                                    ff)
                                                                    tacopt))
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    (uu___1,
                                                                    uu___2,
                                                                    use_eq)))))
                                                                    uu___1)))
                                                                    (fun asc1
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___1 ->
                                                                    (b1,
                                                                    asc1)))))
                                                               uu___1))
                                                 ret_opt))
                                           (fun uu___ ->
                                              (fun ret_opt1 ->
                                                 Obj.magic
                                                   (FStar_Tactics_Effect.tac_bind
                                                      (FStar_Range.mk_range
                                                         "FStar.Tactics.Visit.fst"
                                                         (Prims.of_int (86))
                                                         (Prims.of_int (18))
                                                         (Prims.of_int (86))
                                                         (Prims.of_int (39)))
                                                      (FStar_Range.mk_range
                                                         "FStar.Tactics.Visit.fst"
                                                         (Prims.of_int (87))
                                                         (Prims.of_int (8))
                                                         (Prims.of_int (87))
                                                         (Prims.of_int (31)))
                                                      (Obj.magic
                                                         (FStar_Tactics_Util.map
                                                            (visit_br ff) brs))
                                                      (fun brs1 ->
                                                         FStar_Tactics_Effect.lift_div_tac
                                                           (fun uu___ ->
                                                              FStar_Reflection_Data.Tv_Match
                                                                (sc1,
                                                                  ret_opt1,
                                                                  brs1)))))
                                                uu___))) uu___)))
                    | FStar_Reflection_Data.Tv_AscribedT
                        (e, t1, topt, use_eq) ->
                        Obj.magic
                          (Obj.repr
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Range.mk_range
                                   "FStar.Tactics.Visit.fst"
                                   (Prims.of_int (89)) (Prims.of_int (16))
                                   (Prims.of_int (89)) (Prims.of_int (29)))
                                (FStar_Range.mk_range
                                   "FStar.Tactics.Visit.fst"
                                   (Prims.of_int (90)) (Prims.of_int (8))
                                   (Prims.of_int (91)) (Prims.of_int (36)))
                                (Obj.magic (visit_tm ff e))
                                (fun uu___ ->
                                   (fun e1 ->
                                      Obj.magic
                                        (FStar_Tactics_Effect.tac_bind
                                           (FStar_Range.mk_range
                                              "FStar.Tactics.Visit.fst"
                                              (Prims.of_int (90))
                                              (Prims.of_int (16))
                                              (Prims.of_int (90))
                                              (Prims.of_int (29)))
                                           (FStar_Range.mk_range
                                              "FStar.Tactics.Visit.fst"
                                              (Prims.of_int (91))
                                              (Prims.of_int (8))
                                              (Prims.of_int (91))
                                              (Prims.of_int (36)))
                                           (Obj.magic (visit_tm ff t1))
                                           (fun t2 ->
                                              FStar_Tactics_Effect.lift_div_tac
                                                (fun uu___ ->
                                                   FStar_Reflection_Data.Tv_AscribedT
                                                     (e1, t2, topt, use_eq)))))
                                     uu___)))
                    | FStar_Reflection_Data.Tv_AscribedC (e, c, topt, use_eq)
                        ->
                        Obj.magic
                          (Obj.repr
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Range.mk_range
                                   "FStar.Tactics.Visit.fst"
                                   (Prims.of_int (93)) (Prims.of_int (16))
                                   (Prims.of_int (93)) (Prims.of_int (29)))
                                (FStar_Range.mk_range
                                   "FStar.Tactics.Visit.fst"
                                   (Prims.of_int (94)) (Prims.of_int (8))
                                   (Prims.of_int (94)) (Prims.of_int (36)))
                                (Obj.magic (visit_tm ff e))
                                (fun e1 ->
                                   FStar_Tactics_Effect.lift_div_tac
                                     (fun uu___ ->
                                        FStar_Reflection_Data.Tv_AscribedC
                                          (e1, c, topt, use_eq))))))
                   (fun uu___ ->
                      (fun tv' ->
                         Obj.magic
                           (ff (FStar_Reflection_Builtins.pack_ln tv')))
                        uu___))) uu___)
and (visit_br :
  (FStar_Reflection_Types.term ->
     (FStar_Reflection_Types.term, unit) FStar_Tactics_Effect.tac_repr)
    ->
    FStar_Reflection_Data.branch ->
      (FStar_Reflection_Data.branch, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun ff ->
    fun b ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Range.mk_range "FStar.Tactics.Visit.fst" (Prims.of_int (98))
           (Prims.of_int (15)) (Prims.of_int (98)) (Prims.of_int (16)))
        (FStar_Range.mk_range "FStar.Tactics.Visit.fst" (Prims.of_int (98))
           (Prims.of_int (2)) (Prims.of_int (101)) (Prims.of_int (8)))
        (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> b))
        (fun uu___ ->
           (fun uu___ ->
              match uu___ with
              | (p, t) ->
                  Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Range.mk_range "FStar.Tactics.Visit.fst"
                          (Prims.of_int (99)) (Prims.of_int (10))
                          (Prims.of_int (99)) (Prims.of_int (24)))
                       (FStar_Range.mk_range "FStar.Tactics.Visit.fst"
                          (Prims.of_int (100)) (Prims.of_int (2))
                          (Prims.of_int (101)) (Prims.of_int (8)))
                       (Obj.magic (visit_pat ff p))
                       (fun uu___1 ->
                          (fun p1 ->
                             Obj.magic
                               (FStar_Tactics_Effect.tac_bind
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.Visit.fst"
                                     (Prims.of_int (100)) (Prims.of_int (10))
                                     (Prims.of_int (100)) (Prims.of_int (23)))
                                  (FStar_Range.mk_range
                                     "FStar.Tactics.Visit.fst"
                                     (Prims.of_int (101)) (Prims.of_int (2))
                                     (Prims.of_int (101)) (Prims.of_int (8)))
                                  (Obj.magic (visit_tm ff t))
                                  (fun t1 ->
                                     FStar_Tactics_Effect.lift_div_tac
                                       (fun uu___1 -> (p1, t1))))) uu___1)))
             uu___)
and (visit_pat :
  (FStar_Reflection_Types.term ->
     (FStar_Reflection_Types.term, unit) FStar_Tactics_Effect.tac_repr)
    ->
    FStar_Reflection_Data.pattern ->
      (FStar_Reflection_Data.pattern, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun ff ->
         fun p ->
           match p with
           | FStar_Reflection_Data.Pat_Constant c ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> p)))
           | FStar_Reflection_Data.Pat_Cons (fv, us, l) ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Range.mk_range "FStar.Tactics.Visit.fst"
                          (Prims.of_int (106)) (Prims.of_int (14))
                          (Prims.of_int (106)) (Prims.of_int (55)))
                       (FStar_Range.mk_range "FStar.Tactics.Visit.fst"
                          (Prims.of_int (107)) (Prims.of_int (6))
                          (Prims.of_int (107)) (Prims.of_int (22)))
                       (Obj.magic
                          (FStar_Tactics_Util.map
                             (fun uu___ ->
                                match uu___ with
                                | (p1, b) ->
                                    FStar_Tactics_Effect.tac_bind
                                      (FStar_Range.mk_range
                                         "FStar.Tactics.Visit.fst"
                                         (Prims.of_int (106))
                                         (Prims.of_int (33))
                                         (Prims.of_int (106))
                                         (Prims.of_int (47)))
                                      (FStar_Range.mk_range
                                         "FStar.Tactics.Visit.fst"
                                         (Prims.of_int (106))
                                         (Prims.of_int (32))
                                         (Prims.of_int (106))
                                         (Prims.of_int (51)))
                                      (Obj.magic (visit_pat ff p1))
                                      (fun uu___1 ->
                                         FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___2 -> (uu___1, b)))) l))
                       (fun l1 ->
                          FStar_Tactics_Effect.lift_div_tac
                            (fun uu___ ->
                               FStar_Reflection_Data.Pat_Cons (fv, us, l1)))))
           | FStar_Reflection_Data.Pat_Var bv ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Range.mk_range "FStar.Tactics.Visit.fst"
                          (Prims.of_int (109)) (Prims.of_int (15))
                          (Prims.of_int (109)) (Prims.of_int (42)))
                       (FStar_Range.mk_range "FStar.Tactics.Visit.fst"
                          (Prims.of_int (110)) (Prims.of_int (6))
                          (Prims.of_int (110)) (Prims.of_int (16)))
                       (Obj.magic (on_sort_bv (visit_tm ff) bv))
                       (fun bv1 ->
                          FStar_Tactics_Effect.lift_div_tac
                            (fun uu___ -> FStar_Reflection_Data.Pat_Var bv1))))
           | FStar_Reflection_Data.Pat_Wild bv ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Range.mk_range "FStar.Tactics.Visit.fst"
                          (Prims.of_int (112)) (Prims.of_int (15))
                          (Prims.of_int (112)) (Prims.of_int (42)))
                       (FStar_Range.mk_range "FStar.Tactics.Visit.fst"
                          (Prims.of_int (113)) (Prims.of_int (6))
                          (Prims.of_int (113)) (Prims.of_int (17)))
                       (Obj.magic (on_sort_bv (visit_tm ff) bv))
                       (fun bv1 ->
                          FStar_Tactics_Effect.lift_div_tac
                            (fun uu___ -> FStar_Reflection_Data.Pat_Wild bv1))))
           | FStar_Reflection_Data.Pat_Dot_Term eopt ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Range.mk_range "FStar.Tactics.Visit.fst"
                          (Prims.of_int (115)) (Prims.of_int (19))
                          (Prims.of_int (115)) (Prims.of_int (47)))
                       (FStar_Range.mk_range "FStar.Tactics.Visit.fst"
                          (Prims.of_int (115)) (Prims.of_int (6))
                          (Prims.of_int (115)) (Prims.of_int (47)))
                       (Obj.magic
                          (FStar_Tactics_Util.map_opt (visit_tm ff) eopt))
                       (fun uu___ ->
                          FStar_Tactics_Effect.lift_div_tac
                            (fun uu___1 ->
                               FStar_Reflection_Data.Pat_Dot_Term uu___)))))
        uu___1 uu___
and (visit_comp :
  (FStar_Reflection_Types.term ->
     (FStar_Reflection_Types.term, unit) FStar_Tactics_Effect.tac_repr)
    ->
    FStar_Reflection_Types.comp ->
      (FStar_Reflection_Types.comp, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun ff ->
    fun c ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Range.mk_range "FStar.Tactics.Visit.fst" (Prims.of_int (117))
           (Prims.of_int (11)) (Prims.of_int (117)) (Prims.of_int (25)))
        (FStar_Range.mk_range "FStar.Tactics.Visit.fst" (Prims.of_int (118))
           (Prims.of_int (2)) (Prims.of_int (140)) (Prims.of_int (15)))
        (FStar_Tactics_Effect.lift_div_tac
           (fun uu___ -> FStar_Reflection_Builtins.inspect_comp c))
        (fun uu___ ->
           (fun cv ->
              Obj.magic
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Range.mk_range "FStar.Tactics.Visit.fst"
                      (Prims.of_int (119)) (Prims.of_int (4))
                      (Prims.of_int (138)) (Prims.of_int (35)))
                   (FStar_Range.mk_range "FStar.Tactics.Visit.fst"
                      (Prims.of_int (140)) (Prims.of_int (2))
                      (Prims.of_int (140)) (Prims.of_int (15)))
                   (match cv with
                    | FStar_Reflection_Data.C_Total ret ->
                        Obj.magic
                          (FStar_Tactics_Effect.tac_bind
                             (FStar_Range.mk_range "FStar.Tactics.Visit.fst"
                                (Prims.of_int (121)) (Prims.of_int (18))
                                (Prims.of_int (121)) (Prims.of_int (33)))
                             (FStar_Range.mk_range "FStar.Tactics.Visit.fst"
                                (Prims.of_int (122)) (Prims.of_int (8))
                                (Prims.of_int (122)) (Prims.of_int (19)))
                             (Obj.magic (visit_tm ff ret))
                             (fun ret1 ->
                                FStar_Tactics_Effect.lift_div_tac
                                  (fun uu___ ->
                                     FStar_Reflection_Data.C_Total ret1)))
                    | FStar_Reflection_Data.C_GTotal ret ->
                        Obj.magic
                          (FStar_Tactics_Effect.tac_bind
                             (FStar_Range.mk_range "FStar.Tactics.Visit.fst"
                                (Prims.of_int (125)) (Prims.of_int (18))
                                (Prims.of_int (125)) (Prims.of_int (33)))
                             (FStar_Range.mk_range "FStar.Tactics.Visit.fst"
                                (Prims.of_int (126)) (Prims.of_int (8))
                                (Prims.of_int (126)) (Prims.of_int (20)))
                             (Obj.magic (visit_tm ff ret))
                             (fun ret1 ->
                                FStar_Tactics_Effect.lift_div_tac
                                  (fun uu___ ->
                                     FStar_Reflection_Data.C_GTotal ret1)))
                    | FStar_Reflection_Data.C_Lemma (pre, post, pats) ->
                        Obj.magic
                          (FStar_Tactics_Effect.tac_bind
                             (FStar_Range.mk_range "FStar.Tactics.Visit.fst"
                                (Prims.of_int (129)) (Prims.of_int (18))
                                (Prims.of_int (129)) (Prims.of_int (33)))
                             (FStar_Range.mk_range "FStar.Tactics.Visit.fst"
                                (Prims.of_int (130)) (Prims.of_int (8))
                                (Prims.of_int (132)) (Prims.of_int (29)))
                             (Obj.magic (visit_tm ff pre))
                             (fun uu___ ->
                                (fun pre1 ->
                                   Obj.magic
                                     (FStar_Tactics_Effect.tac_bind
                                        (FStar_Range.mk_range
                                           "FStar.Tactics.Visit.fst"
                                           (Prims.of_int (130))
                                           (Prims.of_int (19))
                                           (Prims.of_int (130))
                                           (Prims.of_int (35)))
                                        (FStar_Range.mk_range
                                           "FStar.Tactics.Visit.fst"
                                           (Prims.of_int (131))
                                           (Prims.of_int (8))
                                           (Prims.of_int (132))
                                           (Prims.of_int (29)))
                                        (Obj.magic (visit_tm ff post))
                                        (fun uu___ ->
                                           (fun post1 ->
                                              Obj.magic
                                                (FStar_Tactics_Effect.tac_bind
                                                   (FStar_Range.mk_range
                                                      "FStar.Tactics.Visit.fst"
                                                      (Prims.of_int (131))
                                                      (Prims.of_int (19))
                                                      (Prims.of_int (131))
                                                      (Prims.of_int (35)))
                                                   (FStar_Range.mk_range
                                                      "FStar.Tactics.Visit.fst"
                                                      (Prims.of_int (132))
                                                      (Prims.of_int (8))
                                                      (Prims.of_int (132))
                                                      (Prims.of_int (29)))
                                                   (Obj.magic
                                                      (visit_tm ff pats))
                                                   (fun pats1 ->
                                                      FStar_Tactics_Effect.lift_div_tac
                                                        (fun uu___ ->
                                                           FStar_Reflection_Data.C_Lemma
                                                             (pre1, post1,
                                                               pats1)))))
                                             uu___))) uu___))
                    | FStar_Reflection_Data.C_Eff (us, eff, res, args, decrs)
                        ->
                        Obj.magic
                          (FStar_Tactics_Effect.tac_bind
                             (FStar_Range.mk_range "FStar.Tactics.Visit.fst"
                                (Prims.of_int (135)) (Prims.of_int (18))
                                (Prims.of_int (135)) (Prims.of_int (33)))
                             (FStar_Range.mk_range "FStar.Tactics.Visit.fst"
                                (Prims.of_int (136)) (Prims.of_int (8))
                                (Prims.of_int (138)) (Prims.of_int (35)))
                             (Obj.magic (visit_tm ff res))
                             (fun uu___ ->
                                (fun res1 ->
                                   Obj.magic
                                     (FStar_Tactics_Effect.tac_bind
                                        (FStar_Range.mk_range
                                           "FStar.Tactics.Visit.fst"
                                           (Prims.of_int (136))
                                           (Prims.of_int (19))
                                           (Prims.of_int (136))
                                           (Prims.of_int (62)))
                                        (FStar_Range.mk_range
                                           "FStar.Tactics.Visit.fst"
                                           (Prims.of_int (137))
                                           (Prims.of_int (8))
                                           (Prims.of_int (138))
                                           (Prims.of_int (35)))
                                        (Obj.magic
                                           (FStar_Tactics_Util.map
                                              (fun uu___ ->
                                                 match uu___ with
                                                 | (a, q) ->
                                                     FStar_Tactics_Effect.tac_bind
                                                       (FStar_Range.mk_range
                                                          "FStar.Tactics.Visit.fst"
                                                          (Prims.of_int (136))
                                                          (Prims.of_int (39))
                                                          (Prims.of_int (136))
                                                          (Prims.of_int (52)))
                                                       (FStar_Range.mk_range
                                                          "FStar.Tactics.Visit.fst"
                                                          (Prims.of_int (136))
                                                          (Prims.of_int (38))
                                                          (Prims.of_int (136))
                                                          (Prims.of_int (56)))
                                                       (Obj.magic
                                                          (visit_tm ff a))
                                                       (fun uu___1 ->
                                                          FStar_Tactics_Effect.lift_div_tac
                                                            (fun uu___2 ->
                                                               (uu___1, q))))
                                              args))
                                        (fun uu___ ->
                                           (fun args1 ->
                                              Obj.magic
                                                (FStar_Tactics_Effect.tac_bind
                                                   (FStar_Range.mk_range
                                                      "FStar.Tactics.Visit.fst"
                                                      (Prims.of_int (137))
                                                      (Prims.of_int (20))
                                                      (Prims.of_int (137))
                                                      (Prims.of_int (43)))
                                                   (FStar_Range.mk_range
                                                      "FStar.Tactics.Visit.fst"
                                                      (Prims.of_int (138))
                                                      (Prims.of_int (8))
                                                      (Prims.of_int (138))
                                                      (Prims.of_int (35)))
                                                   (Obj.magic
                                                      (FStar_Tactics_Util.map
                                                         (visit_tm ff) decrs))
                                                   (fun decrs1 ->
                                                      FStar_Tactics_Effect.lift_div_tac
                                                        (fun uu___ ->
                                                           FStar_Reflection_Data.C_Eff
                                                             (us, eff, res1,
                                                               args1, decrs1)))))
                                             uu___))) uu___)))
                   (fun cv' ->
                      FStar_Tactics_Effect.lift_div_tac
                        (fun uu___ -> FStar_Reflection_Builtins.pack_comp cv'))))
             uu___)