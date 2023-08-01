open Prims
let rec (collect_arr' :
  FStar_Tactics_NamedView.binder Prims.list ->
    FStar_Tactics_NamedView.comp ->
      ((FStar_Tactics_NamedView.binder Prims.list *
         FStar_Tactics_NamedView.comp),
        unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun bs ->
         fun c ->
           match c with
           | FStar_Reflection_V2_Data.C_Total t ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "FStar.Tactics.V2.SyntaxHelpers.fst"
                                (Prims.of_int (15)) (Prims.of_int (20))
                                (Prims.of_int (15)) (Prims.of_int (29)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "FStar.Tactics.V2.SyntaxHelpers.fst"
                                (Prims.of_int (15)) (Prims.of_int (14))
                                (Prims.of_int (19)) (Prims.of_int (19)))))
                       (Obj.magic (FStar_Tactics_NamedView.inspect t))
                       (fun uu___ ->
                          (fun uu___ ->
                             match uu___ with
                             | FStar_Tactics_NamedView.Tv_Arrow (b, c1) ->
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
    ((FStar_Tactics_NamedView.binder Prims.list *
       FStar_Tactics_NamedView.comp),
      unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.SyntaxHelpers.fst"
               (Prims.of_int (26)) (Prims.of_int (18)) (Prims.of_int (26))
               (Prims.of_int (45)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.SyntaxHelpers.fst"
               (Prims.of_int (25)) (Prims.of_int (22)) (Prims.of_int (27))
               (Prims.of_int (29)))))
      (Obj.magic (collect_arr' [] (FStar_Reflection_V2_Data.C_Total t)))
      (fun uu___ ->
         FStar_Tactics_Effect.lift_div_tac
           (fun uu___1 ->
              match uu___ with | (bs, c) -> ((FStar_List_Tot_Base.rev bs), c)))
let (collect_arr :
  FStar_Reflection_Types.typ ->
    ((FStar_Reflection_Types.typ Prims.list * FStar_Tactics_NamedView.comp),
      unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.SyntaxHelpers.fst"
               (Prims.of_int (31)) (Prims.of_int (18)) (Prims.of_int (31))
               (Prims.of_int (45)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.SyntaxHelpers.fst"
               (Prims.of_int (30)) (Prims.of_int (19)) (Prims.of_int (33))
               (Prims.of_int (29)))))
      (Obj.magic (collect_arr' [] (FStar_Reflection_V2_Data.C_Total t)))
      (fun uu___ ->
         FStar_Tactics_Effect.lift_div_tac
           (fun uu___1 ->
              match uu___ with
              | (bs, c) ->
                  ((FStar_List_Tot_Base.rev
                      (FStar_List_Tot_Base.map
                         (fun b -> b.FStar_Tactics_NamedView.sort) bs)), c)))
let rec (collect_abs' :
  FStar_Tactics_NamedView.binder Prims.list ->
    FStar_Tactics_NamedView.term ->
      ((FStar_Tactics_NamedView.binder Prims.list *
         FStar_Tactics_NamedView.term),
        unit) FStar_Tactics_Effect.tac_repr)
  =
  fun bs ->
    fun t ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.V2.SyntaxHelpers.fst"
                 (Prims.of_int (37)) (Prims.of_int (10)) (Prims.of_int (37))
                 (Prims.of_int (19)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.V2.SyntaxHelpers.fst"
                 (Prims.of_int (37)) (Prims.of_int (4)) (Prims.of_int (40))
                 (Prims.of_int (18)))))
        (Obj.magic (FStar_Tactics_NamedView.inspect t))
        (fun uu___ ->
           (fun uu___ ->
              match uu___ with
              | FStar_Tactics_NamedView.Tv_Abs (b, t') ->
                  Obj.magic (Obj.repr (collect_abs' (b :: bs) t'))
              | uu___1 ->
                  Obj.magic
                    (Obj.repr
                       (FStar_Tactics_Effect.lift_div_tac
                          (fun uu___2 -> (bs, t))))) uu___)
let (collect_abs :
  FStar_Tactics_NamedView.term ->
    ((FStar_Tactics_NamedView.binder Prims.list *
       FStar_Tactics_NamedView.term),
      unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.SyntaxHelpers.fst"
               (Prims.of_int (44)) (Prims.of_int (19)) (Prims.of_int (44))
               (Prims.of_int (36)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.SyntaxHelpers.fst"
               (Prims.of_int (43)) (Prims.of_int (19)) (Prims.of_int (45))
               (Prims.of_int (30))))) (Obj.magic (collect_abs' [] t))
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
  FStar_Tactics_NamedView.binder Prims.list ->
    FStar_Tactics_NamedView.comp ->
      (FStar_Tactics_NamedView.term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun bs ->
         fun cod ->
           match bs with
           | [] -> Obj.magic (Obj.repr (fail "mk_arr, empty binders"))
           | b::[] ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.lift_div_tac
                       (fun uu___ ->
                          FStar_Tactics_NamedView.pack
                            (FStar_Tactics_NamedView.Tv_Arrow (b, cod)))))
           | b::bs1 ->
               Obj.magic
                 (Obj.repr
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "FStar.Tactics.V2.SyntaxHelpers.fst"
                                (Prims.of_int (56)) (Prims.of_int (11))
                                (Prims.of_int (56)) (Prims.of_int (49)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range " dummy" Prims.int_zero
                                Prims.int_zero Prims.int_zero Prims.int_zero)))
                       (Obj.magic
                          (FStar_Tactics_Effect.tac_bind
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "FStar.Tactics.V2.SyntaxHelpers.fst"
                                      (Prims.of_int (56)) (Prims.of_int (23))
                                      (Prims.of_int (56)) (Prims.of_int (48)))))
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "FStar.Tactics.V2.SyntaxHelpers.fst"
                                      (Prims.of_int (56)) (Prims.of_int (11))
                                      (Prims.of_int (56)) (Prims.of_int (49)))))
                             (Obj.magic
                                (FStar_Tactics_Effect.tac_bind
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "FStar.Tactics.V2.SyntaxHelpers.fst"
                                            (Prims.of_int (56))
                                            (Prims.of_int (32))
                                            (Prims.of_int (56))
                                            (Prims.of_int (47)))))
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "FStar.Tactics.V2.SyntaxHelpers.fst"
                                            (Prims.of_int (56))
                                            (Prims.of_int (23))
                                            (Prims.of_int (56))
                                            (Prims.of_int (48)))))
                                   (Obj.magic (mk_arr bs1 cod))
                                   (fun uu___ ->
                                      FStar_Tactics_Effect.lift_div_tac
                                        (fun uu___1 ->
                                           FStar_Reflection_V2_Data.C_Total
                                             uu___))))
                             (fun uu___ ->
                                FStar_Tactics_Effect.lift_div_tac
                                  (fun uu___1 ->
                                     FStar_Tactics_NamedView.Tv_Arrow
                                       (b, uu___)))))
                       (fun uu___ ->
                          FStar_Tactics_Effect.lift_div_tac
                            (fun uu___1 -> FStar_Tactics_NamedView.pack uu___)))))
        uu___1 uu___
let rec (mk_tot_arr :
  FStar_Tactics_NamedView.binder Prims.list ->
    FStar_Tactics_NamedView.term ->
      (FStar_Tactics_NamedView.term, unit) FStar_Tactics_Effect.tac_repr)
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
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "FStar.Tactics.V2.SyntaxHelpers.fst"
                                (Prims.of_int (62)) (Prims.of_int (11))
                                (Prims.of_int (62)) (Prims.of_int (53)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range " dummy" Prims.int_zero
                                Prims.int_zero Prims.int_zero Prims.int_zero)))
                       (Obj.magic
                          (FStar_Tactics_Effect.tac_bind
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "FStar.Tactics.V2.SyntaxHelpers.fst"
                                      (Prims.of_int (62)) (Prims.of_int (23))
                                      (Prims.of_int (62)) (Prims.of_int (52)))))
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "FStar.Tactics.V2.SyntaxHelpers.fst"
                                      (Prims.of_int (62)) (Prims.of_int (11))
                                      (Prims.of_int (62)) (Prims.of_int (53)))))
                             (Obj.magic
                                (FStar_Tactics_Effect.tac_bind
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "FStar.Tactics.V2.SyntaxHelpers.fst"
                                            (Prims.of_int (62))
                                            (Prims.of_int (32))
                                            (Prims.of_int (62))
                                            (Prims.of_int (51)))))
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "FStar.Tactics.V2.SyntaxHelpers.fst"
                                            (Prims.of_int (62))
                                            (Prims.of_int (23))
                                            (Prims.of_int (62))
                                            (Prims.of_int (52)))))
                                   (Obj.magic (mk_tot_arr bs1 cod))
                                   (fun uu___ ->
                                      FStar_Tactics_Effect.lift_div_tac
                                        (fun uu___1 ->
                                           FStar_Reflection_V2_Data.C_Total
                                             uu___))))
                             (fun uu___ ->
                                FStar_Tactics_Effect.lift_div_tac
                                  (fun uu___1 ->
                                     FStar_Tactics_NamedView.Tv_Arrow
                                       (b, uu___)))))
                       (fun uu___ ->
                          FStar_Tactics_Effect.lift_div_tac
                            (fun uu___1 -> FStar_Tactics_NamedView.pack uu___)))))
        uu___1 uu___
let (lookup_lb :
  FStar_Tactics_NamedView.letbinding Prims.list ->
    FStar_Reflection_Types.name ->
      (FStar_Tactics_NamedView.letbinding, unit)
        FStar_Tactics_Effect.tac_repr)
  =
  fun lbs ->
    fun nm ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.V2.SyntaxHelpers.fst"
                 (Prims.of_int (65)) (Prims.of_int (10)) (Prims.of_int (67))
                 (Prims.of_int (16)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.V2.SyntaxHelpers.fst"
                 (Prims.of_int (69)) (Prims.of_int (2)) (Prims.of_int (71))
                 (Prims.of_int (59)))))
        (FStar_Tactics_Effect.lift_div_tac
           (fun uu___ ->
              FStar_List_Tot_Base.find
                (fun lb ->
                   (FStar_Reflection_V2_Builtins.inspect_fv
                      lb.FStar_Tactics_NamedView.lb_fv)
                     = nm) lbs))
        (fun uu___ ->
           (fun o ->
              match o with
              | FStar_Pervasives_Native.Some lb ->
                  Obj.magic
                    (Obj.repr
                       (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> lb)))
              | FStar_Pervasives_Native.None ->
                  Obj.magic
                    (Obj.repr
                       (fail "lookup_letbinding: Name not in let group")))
             uu___)
let rec (inspect_unascribe :
  FStar_Tactics_NamedView.term ->
    (FStar_Tactics_NamedView.term_view, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.SyntaxHelpers.fst"
               (Prims.of_int (74)) (Prims.of_int (8)) (Prims.of_int (74))
               (Prims.of_int (17)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.V2.SyntaxHelpers.fst"
               (Prims.of_int (74)) (Prims.of_int (2)) (Prims.of_int (78))
               (Prims.of_int (12)))))
      (Obj.magic (FStar_Tactics_NamedView.inspect t))
      (fun uu___ ->
         (fun uu___ ->
            match uu___ with
            | FStar_Tactics_NamedView.Tv_AscribedT
                (t1, uu___1, uu___2, uu___3) ->
                Obj.magic (Obj.repr (inspect_unascribe t1))
            | FStar_Tactics_NamedView.Tv_AscribedC
                (t1, uu___1, uu___2, uu___3) ->
                Obj.magic (Obj.repr (inspect_unascribe t1))
            | tv ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> tv))))
           uu___)
let rec (collect_app' :
  FStar_Reflection_V2_Data.argv Prims.list ->
    FStar_Tactics_NamedView.term ->
      ((FStar_Tactics_NamedView.term * FStar_Reflection_V2_Data.argv
         Prims.list),
        unit) FStar_Tactics_Effect.tac_repr)
  =
  fun args ->
    fun t ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.V2.SyntaxHelpers.fst"
                 (Prims.of_int (83)) (Prims.of_int (10)) (Prims.of_int (83))
                 (Prims.of_int (29)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.V2.SyntaxHelpers.fst"
                 (Prims.of_int (83)) (Prims.of_int (4)) (Prims.of_int (86))
                 (Prims.of_int (20))))) (Obj.magic (inspect_unascribe t))
        (fun uu___ ->
           (fun uu___ ->
              match uu___ with
              | FStar_Tactics_NamedView.Tv_App (l, r) ->
                  Obj.magic (Obj.repr (collect_app' (r :: args) l))
              | uu___1 ->
                  Obj.magic
                    (Obj.repr
                       (FStar_Tactics_Effect.lift_div_tac
                          (fun uu___2 -> (t, args))))) uu___)
let (collect_app :
  FStar_Tactics_NamedView.term ->
    ((FStar_Tactics_NamedView.term * FStar_Reflection_V2_Data.argv
       Prims.list),
      unit) FStar_Tactics_Effect.tac_repr)
  = collect_app' []