open Prims
let rec (collect_arr' :
  FStar_Reflection_Types.binder Prims.list ->
    FStar_Reflection_Types.comp ->
      ((FStar_Reflection_Types.binder Prims.list *
         FStar_Reflection_Types.comp),
        unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun bs ->
         fun c ->
           match FStar_Reflection_Builtins.inspect_comp c with
           | FStar_Reflection_Data.C_Total t ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.tac_bind
                       (Prims.mk_range "FStar.Tactics.SyntaxHelpers.fst"
                          (Prims.of_int (14)) (Prims.of_int (20))
                          (Prims.of_int (14)) (Prims.of_int (29)))
                       (Prims.mk_range "FStar.Tactics.SyntaxHelpers.fst"
                          (Prims.of_int (14)) (Prims.of_int (14))
                          (Prims.of_int (18)) (Prims.of_int (19)))
                       (Obj.magic (FStar_Tactics_Builtins.inspect t))
                       (fun uu___ ->
                          (fun uu___ ->
                             match uu___ with
                             | FStar_Reflection_Data.Tv_Arrow (b, c1) ->
                                 Obj.magic
                                   (Obj.repr (collect_arr' (b :: bs) c1))
                             | uu___1 ->
                                 Obj.magic
                                   (Obj.repr
                                      (FStar_Tactics_Effect.lift_div_tac
                                         (fun uu___2 -> (bs, c))))) uu___)))
           | uu___ ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.lift_div_tac
                       (fun uu___1 -> (bs, c))))) uu___1 uu___
let (collect_arr_bs :
  FStar_Reflection_Types.typ ->
    ((FStar_Reflection_Types.binder Prims.list * FStar_Reflection_Types.comp),
      unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    FStar_Tactics_Effect.tac_bind
      (Prims.mk_range "FStar.Tactics.SyntaxHelpers.fst" (Prims.of_int (25))
         (Prims.of_int (18)) (Prims.of_int (25)) (Prims.of_int (57)))
      (Prims.mk_range "FStar.Tactics.SyntaxHelpers.fst" (Prims.of_int (25))
         (Prims.of_int (4)) (Prims.of_int (26)) (Prims.of_int (29)))
      (Obj.magic
         (collect_arr' []
            (FStar_Reflection_Builtins.pack_comp
               (FStar_Reflection_Data.C_Total t))))
      (fun uu___ ->
         FStar_Tactics_Effect.lift_div_tac
           (fun uu___1 ->
              match uu___ with | (bs, c) -> ((FStar_List_Tot_Base.rev bs), c)))
let (collect_arr :
  FStar_Reflection_Types.typ ->
    ((FStar_Reflection_Types.typ Prims.list * FStar_Reflection_Types.comp),
      unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    FStar_Tactics_Effect.tac_bind
      (Prims.mk_range "FStar.Tactics.SyntaxHelpers.fst" (Prims.of_int (30))
         (Prims.of_int (18)) (Prims.of_int (30)) (Prims.of_int (57)))
      (Prims.mk_range "FStar.Tactics.SyntaxHelpers.fst" (Prims.of_int (30))
         (Prims.of_int (4)) (Prims.of_int (32)) (Prims.of_int (29)))
      (Obj.magic
         (collect_arr' []
            (FStar_Reflection_Builtins.pack_comp
               (FStar_Reflection_Data.C_Total t))))
      (fun uu___ ->
         FStar_Tactics_Effect.lift_div_tac
           (fun uu___1 ->
              match uu___ with
              | (bs, c) ->
                  ((FStar_List_Tot_Base.rev
                      (FStar_List_Tot_Base.map
                         FStar_Reflection_Derived.type_of_binder bs)), c)))
let rec (collect_abs' :
  FStar_Reflection_Types.binder Prims.list ->
    FStar_Reflection_Types.term ->
      ((FStar_Reflection_Types.binder Prims.list *
         FStar_Reflection_Types.term),
        unit) FStar_Tactics_Effect.tac_repr)
  =
  fun bs ->
    fun t ->
      FStar_Tactics_Effect.tac_bind
        (Prims.mk_range "FStar.Tactics.SyntaxHelpers.fst" (Prims.of_int (36))
           (Prims.of_int (10)) (Prims.of_int (36)) (Prims.of_int (19)))
        (Prims.mk_range "FStar.Tactics.SyntaxHelpers.fst" (Prims.of_int (36))
           (Prims.of_int (4)) (Prims.of_int (39)) (Prims.of_int (18)))
        (Obj.magic (FStar_Tactics_Builtins.inspect t))
        (fun uu___ ->
           (fun uu___ ->
              match uu___ with
              | FStar_Reflection_Data.Tv_Abs (b, t') ->
                  Obj.magic (Obj.repr (collect_abs' (b :: bs) t'))
              | uu___1 ->
                  Obj.magic
                    (Obj.repr
                       (FStar_Tactics_Effect.lift_div_tac
                          (fun uu___2 -> (bs, t))))) uu___)
let (collect_abs :
  FStar_Reflection_Types.term ->
    ((FStar_Reflection_Types.binder Prims.list * FStar_Reflection_Types.term),
      unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    FStar_Tactics_Effect.tac_bind
      (Prims.mk_range "FStar.Tactics.SyntaxHelpers.fst" (Prims.of_int (43))
         (Prims.of_int (19)) (Prims.of_int (43)) (Prims.of_int (36)))
      (Prims.mk_range "FStar.Tactics.SyntaxHelpers.fst" (Prims.of_int (43))
         (Prims.of_int (4)) (Prims.of_int (44)) (Prims.of_int (30)))
      (Obj.magic (collect_abs' [] t))
      (fun uu___ ->
         FStar_Tactics_Effect.lift_div_tac
           (fun uu___1 ->
              match uu___ with
              | (bs, t') -> ((FStar_List_Tot_Base.rev bs), t')))
let fail : 'a . Prims.string -> ('a, unit) FStar_Tactics_Effect.tac_repr =
  fun uu___ ->
    (fun m ->
       Obj.magic
         (FStar_Tactics_Effect.raise (FStar_Tactics_Common.TacticFailure m)))
      uu___
let rec (mk_arr :
  FStar_Reflection_Types.binder Prims.list ->
    FStar_Reflection_Types.comp ->
      (FStar_Reflection_Types.term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun bs ->
    fun cod ->
      match bs with
      | [] -> fail "mk_arr, empty binders"
      | b::[] ->
          FStar_Tactics_Builtins.pack
            (FStar_Reflection_Data.Tv_Arrow (b, cod))
      | b::bs1 ->
          FStar_Tactics_Effect.tac_bind
            (Prims.mk_range "FStar.Tactics.SyntaxHelpers.fst"
               (Prims.of_int (55)) (Prims.of_int (11)) (Prims.of_int (55))
               (Prims.of_int (61)))
            (Prims.mk_range "FStar.Tactics.SyntaxHelpers.fst"
               (Prims.of_int (55)) (Prims.of_int (6)) (Prims.of_int (55))
               (Prims.of_int (61)))
            (Obj.magic
               (FStar_Tactics_Effect.tac_bind
                  (Prims.mk_range "FStar.Tactics.SyntaxHelpers.fst"
                     (Prims.of_int (55)) (Prims.of_int (23))
                     (Prims.of_int (55)) (Prims.of_int (60)))
                  (Prims.mk_range "FStar.Tactics.SyntaxHelpers.fst"
                     (Prims.of_int (55)) (Prims.of_int (11))
                     (Prims.of_int (55)) (Prims.of_int (61)))
                  (Obj.magic
                     (FStar_Tactics_Effect.tac_bind
                        (Prims.mk_range "FStar.Tactics.SyntaxHelpers.fst"
                           (Prims.of_int (55)) (Prims.of_int (34))
                           (Prims.of_int (55)) (Prims.of_int (59)))
                        (Prims.mk_range "FStar.Tactics.SyntaxHelpers.fst"
                           (Prims.of_int (55)) (Prims.of_int (23))
                           (Prims.of_int (55)) (Prims.of_int (60)))
                        (Obj.magic
                           (FStar_Tactics_Effect.tac_bind
                              (Prims.mk_range
                                 "FStar.Tactics.SyntaxHelpers.fst"
                                 (Prims.of_int (55)) (Prims.of_int (43))
                                 (Prims.of_int (55)) (Prims.of_int (58)))
                              (Prims.mk_range
                                 "FStar.Tactics.SyntaxHelpers.fst"
                                 (Prims.of_int (55)) (Prims.of_int (34))
                                 (Prims.of_int (55)) (Prims.of_int (59)))
                              (Obj.magic (mk_arr bs1 cod))
                              (fun uu___ ->
                                 FStar_Tactics_Effect.lift_div_tac
                                   (fun uu___1 ->
                                      FStar_Reflection_Data.C_Total uu___))))
                        (fun uu___ ->
                           FStar_Tactics_Effect.lift_div_tac
                             (fun uu___1 ->
                                FStar_Reflection_Builtins.pack_comp uu___))))
                  (fun uu___ ->
                     FStar_Tactics_Effect.lift_div_tac
                       (fun uu___1 ->
                          FStar_Reflection_Data.Tv_Arrow (b, uu___)))))
            (fun uu___ ->
               (fun uu___ -> Obj.magic (FStar_Tactics_Builtins.pack uu___))
                 uu___)
let rec (mk_arr_curried :
  FStar_Reflection_Types.binder Prims.list ->
    FStar_Reflection_Types.comp ->
      (FStar_Reflection_Types.term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun bs ->
    fun cod ->
      match bs with
      | [] -> fail "mk_arr, empty binders"
      | b::[] ->
          FStar_Tactics_Builtins.pack_curried
            (FStar_Reflection_Data.Tv_Arrow (b, cod))
      | b::bs1 ->
          FStar_Tactics_Effect.tac_bind
            (Prims.mk_range "FStar.Tactics.SyntaxHelpers.fst"
               (Prims.of_int (61)) (Prims.of_int (30)) (Prims.of_int (61))
               (Prims.of_int (88)))
            (Prims.mk_range "FStar.Tactics.SyntaxHelpers.fst"
               (Prims.of_int (61)) (Prims.of_int (17)) (Prims.of_int (61))
               (Prims.of_int (88)))
            (Obj.magic
               (FStar_Tactics_Effect.tac_bind
                  (Prims.mk_range "FStar.Tactics.SyntaxHelpers.fst"
                     (Prims.of_int (61)) (Prims.of_int (42))
                     (Prims.of_int (61)) (Prims.of_int (87)))
                  (Prims.mk_range "FStar.Tactics.SyntaxHelpers.fst"
                     (Prims.of_int (61)) (Prims.of_int (30))
                     (Prims.of_int (61)) (Prims.of_int (88)))
                  (Obj.magic
                     (FStar_Tactics_Effect.tac_bind
                        (Prims.mk_range "FStar.Tactics.SyntaxHelpers.fst"
                           (Prims.of_int (61)) (Prims.of_int (53))
                           (Prims.of_int (61)) (Prims.of_int (86)))
                        (Prims.mk_range "FStar.Tactics.SyntaxHelpers.fst"
                           (Prims.of_int (61)) (Prims.of_int (42))
                           (Prims.of_int (61)) (Prims.of_int (87)))
                        (Obj.magic
                           (FStar_Tactics_Effect.tac_bind
                              (Prims.mk_range
                                 "FStar.Tactics.SyntaxHelpers.fst"
                                 (Prims.of_int (61)) (Prims.of_int (62))
                                 (Prims.of_int (61)) (Prims.of_int (85)))
                              (Prims.mk_range
                                 "FStar.Tactics.SyntaxHelpers.fst"
                                 (Prims.of_int (61)) (Prims.of_int (53))
                                 (Prims.of_int (61)) (Prims.of_int (86)))
                              (Obj.magic (mk_arr_curried bs1 cod))
                              (fun uu___ ->
                                 FStar_Tactics_Effect.lift_div_tac
                                   (fun uu___1 ->
                                      FStar_Reflection_Data.C_Total uu___))))
                        (fun uu___ ->
                           FStar_Tactics_Effect.lift_div_tac
                             (fun uu___1 ->
                                FStar_Reflection_Builtins.pack_comp uu___))))
                  (fun uu___ ->
                     FStar_Tactics_Effect.lift_div_tac
                       (fun uu___1 ->
                          FStar_Reflection_Data.Tv_Arrow (b, uu___)))))
            (fun uu___ ->
               (fun uu___ ->
                  Obj.magic (FStar_Tactics_Builtins.pack_curried uu___))
                 uu___)
let rec (mk_tot_arr :
  FStar_Reflection_Types.binder Prims.list ->
    FStar_Reflection_Types.term ->
      (FStar_Reflection_Types.term, unit) FStar_Tactics_Effect.tac_repr)
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
                    (FStar_Tactics_Effect.tac_bind
                       (Prims.mk_range "FStar.Tactics.SyntaxHelpers.fst"
                          (Prims.of_int (67)) (Prims.of_int (11))
                          (Prims.of_int (67)) (Prims.of_int (65)))
                       (Prims.mk_range "FStar.Tactics.SyntaxHelpers.fst"
                          (Prims.of_int (67)) (Prims.of_int (6))
                          (Prims.of_int (67)) (Prims.of_int (65)))
                       (Obj.magic
                          (FStar_Tactics_Effect.tac_bind
                             (Prims.mk_range
                                "FStar.Tactics.SyntaxHelpers.fst"
                                (Prims.of_int (67)) (Prims.of_int (23))
                                (Prims.of_int (67)) (Prims.of_int (64)))
                             (Prims.mk_range
                                "FStar.Tactics.SyntaxHelpers.fst"
                                (Prims.of_int (67)) (Prims.of_int (11))
                                (Prims.of_int (67)) (Prims.of_int (65)))
                             (Obj.magic
                                (FStar_Tactics_Effect.tac_bind
                                   (Prims.mk_range
                                      "FStar.Tactics.SyntaxHelpers.fst"
                                      (Prims.of_int (67)) (Prims.of_int (34))
                                      (Prims.of_int (67)) (Prims.of_int (63)))
                                   (Prims.mk_range
                                      "FStar.Tactics.SyntaxHelpers.fst"
                                      (Prims.of_int (67)) (Prims.of_int (23))
                                      (Prims.of_int (67)) (Prims.of_int (64)))
                                   (Obj.magic
                                      (FStar_Tactics_Effect.tac_bind
                                         (Prims.mk_range
                                            "FStar.Tactics.SyntaxHelpers.fst"
                                            (Prims.of_int (67))
                                            (Prims.of_int (43))
                                            (Prims.of_int (67))
                                            (Prims.of_int (62)))
                                         (Prims.mk_range
                                            "FStar.Tactics.SyntaxHelpers.fst"
                                            (Prims.of_int (67))
                                            (Prims.of_int (34))
                                            (Prims.of_int (67))
                                            (Prims.of_int (63)))
                                         (Obj.magic (mk_tot_arr bs1 cod))
                                         (fun uu___ ->
                                            FStar_Tactics_Effect.lift_div_tac
                                              (fun uu___1 ->
                                                 FStar_Reflection_Data.C_Total
                                                   uu___))))
                                   (fun uu___ ->
                                      FStar_Tactics_Effect.lift_div_tac
                                        (fun uu___1 ->
                                           FStar_Reflection_Builtins.pack_comp
                                             uu___))))
                             (fun uu___ ->
                                FStar_Tactics_Effect.lift_div_tac
                                  (fun uu___1 ->
                                     FStar_Reflection_Data.Tv_Arrow
                                       (b, uu___)))))
                       (fun uu___ ->
                          (fun uu___ ->
                             Obj.magic (FStar_Tactics_Builtins.pack uu___))
                            uu___)))) uu___1 uu___
let (lookup_lb_view :
  FStar_Reflection_Types.letbinding Prims.list ->
    FStar_Reflection_Types.name ->
      (FStar_Reflection_Data.lb_view, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun lbs ->
    fun nm ->
      FStar_Tactics_Effect.tac_bind
        (Prims.mk_range "FStar.Tactics.SyntaxHelpers.fst" (Prims.of_int (70))
           (Prims.of_int (10)) (Prims.of_int (74)) (Prims.of_int (16)))
        (Prims.mk_range "FStar.Tactics.SyntaxHelpers.fst" (Prims.of_int (76))
           (Prims.of_int (2)) (Prims.of_int (78)) (Prims.of_int (56)))
        (FStar_Tactics_Effect.lift_div_tac
           (fun uu___ ->
              FStar_List_Tot_Base.find
                (fun lb ->
                   (FStar_Reflection_Builtins.inspect_fv
                      (FStar_Reflection_Builtins.inspect_lb lb).FStar_Reflection_Data.lb_fv)
                     = nm) lbs))
        (fun uu___ ->
           (fun o ->
              match o with
              | FStar_Pervasives_Native.Some lb ->
                  Obj.magic
                    (Obj.repr
                       (FStar_Tactics_Effect.lift_div_tac
                          (fun uu___ ->
                             FStar_Reflection_Builtins.inspect_lb lb)))
              | FStar_Pervasives_Native.None ->
                  Obj.magic
                    (Obj.repr (fail "lookup_lb_view: Name not in let group")))
             uu___)