open Prims
let rec _split_subst_at_bv :
  'a 'b .
    FStar_Reflection_Types.bv ->
      ((FStar_Reflection_Types.bv * 'a) * 'b) Prims.list ->
        (((FStar_Reflection_Types.bv * 'a) * 'b) Prims.list *
          ((FStar_Reflection_Types.bv * 'a) * 'b) Prims.list)
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
      FStar_Reflection_Types.bv FStar_Pervasives_Native.option ->
        FStar_InteractiveHelpers_Propositions.assertions ->
          ((FStar_InteractiveHelpers_Base.genv *
             FStar_InteractiveHelpers_Propositions.assertions),
            unit) FStar_Tactics_Effect.tac_repr)
  =
  fun dbg ->
    fun ge ->
      fun shadowed_bv ->
        fun es ->
          FStar_Tactics_Effect.tac_bind
            (FStar_Range.mk_range "FStar.InteractiveHelpers.Output.fst"
               (Prims.of_int (44)) (Prims.of_int (2)) (Prims.of_int (44))
               (Prims.of_int (80)))
            (FStar_Range.mk_range "FStar.InteractiveHelpers.Output.fst"
               (Prims.of_int (46)) (Prims.of_int (2)) (Prims.of_int (73))
               (Prims.of_int (31)))
            (Obj.magic
               (FStar_Tactics_Effect.tac_bind
                  (FStar_Range.mk_range "FStar.InteractiveHelpers.Output.fst"
                     (Prims.of_int (44)) (Prims.of_int (16))
                     (Prims.of_int (44)) (Prims.of_int (80)))
                  (FStar_Range.mk_range "FStar.InteractiveHelpers.Output.fst"
                     (Prims.of_int (44)) (Prims.of_int (2))
                     (Prims.of_int (44)) (Prims.of_int (80)))
                  (Obj.magic
                     (FStar_Tactics_Effect.tac_bind
                        (FStar_Range.mk_range
                           "FStar.InteractiveHelpers.Output.fst"
                           (Prims.of_int (44)) (Prims.of_int (62))
                           (Prims.of_int (44)) (Prims.of_int (79)))
                        (FStar_Range.mk_range "prims.fst"
                           (Prims.of_int (590)) (Prims.of_int (19))
                           (Prims.of_int (590)) (Prims.of_int (31)))
                        (Obj.magic
                           (FStar_InteractiveHelpers_Base.genv_to_string ge))
                        (fun uu___ ->
                           FStar_Tactics_Effect.lift_div_tac
                             (fun uu___1 ->
                                Prims.strcat
                                  "subst_shadowed_with_abs_in_assertions:\n"
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
                       (FStar_Range.mk_range
                          "FStar.InteractiveHelpers.Output.fst"
                          (Prims.of_int (46)) (Prims.of_int (19))
                          (Prims.of_int (46)) (Prims.of_int (45)))
                       (FStar_Range.mk_range
                          "FStar.InteractiveHelpers.Output.fst"
                          (Prims.of_int (46)) (Prims.of_int (2))
                          (Prims.of_int (73)) (Prims.of_int (31)))
                       (Obj.magic
                          (FStar_InteractiveHelpers_Base.generate_shadowed_subst
                             ge))
                       (fun uu___1 ->
                          (fun uu___1 ->
                             match uu___1 with
                             | (ge1, subst) ->
                                 Obj.magic
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Range.mk_range
                                         "FStar.InteractiveHelpers.Output.fst"
                                         (Prims.of_int (47))
                                         (Prims.of_int (19))
                                         (Prims.of_int (47))
                                         (Prims.of_int (81)))
                                      (FStar_Range.mk_range
                                         "FStar.InteractiveHelpers.Output.fst"
                                         (Prims.of_int (53))
                                         (Prims.of_int (2))
                                         (Prims.of_int (73))
                                         (Prims.of_int (31)))
                                      (Obj.magic
                                         (FStar_Tactics_Util.map
                                            (fun uu___2 ->
                                               match uu___2 with
                                               | (src, ty, tgt) ->
                                                   FStar_Tactics_Effect.tac_bind
                                                     (FStar_Range.mk_range
                                                        "FStar.InteractiveHelpers.Output.fst"
                                                        (Prims.of_int (47))
                                                        (Prims.of_int (57))
                                                        (Prims.of_int (47))
                                                        (Prims.of_int (74)))
                                                     (FStar_Range.mk_range
                                                        "FStar.InteractiveHelpers.Output.fst"
                                                        (Prims.of_int (47))
                                                        (Prims.of_int (46))
                                                        (Prims.of_int (47))
                                                        (Prims.of_int (74)))
                                                     (Obj.magic
                                                        (FStar_Tactics_Builtins.pack
                                                           (FStar_Reflection_Data.Tv_Var
                                                              tgt)))
                                                     (fun uu___3 ->
                                                        FStar_Tactics_Effect.lift_div_tac
                                                          (fun uu___4 ->
                                                             ((src, ty),
                                                               uu___3))))
                                            subst))
                                      (fun uu___2 ->
                                         (fun post_subst ->
                                            Obj.magic
                                              (FStar_Tactics_Effect.tac_bind
                                                 (FStar_Range.mk_range
                                                    "FStar.InteractiveHelpers.Output.fst"
                                                    (Prims.of_int (54))
                                                    (Prims.of_int (4))
                                                    (Prims.of_int (55))
                                                    (Prims.of_int (19)))
                                                 (FStar_Range.mk_range
                                                    "FStar.InteractiveHelpers.Output.fst"
                                                    (Prims.of_int (57))
                                                    (Prims.of_int (2))
                                                    (Prims.of_int (73))
                                                    (Prims.of_int (31)))
                                                 (FStar_Tactics_Effect.lift_div_tac
                                                    (fun uu___2 ->
                                                       if
                                                         FStar_Pervasives_Native.uu___is_Some
                                                           shadowed_bv
                                                       then
                                                         FStar_Pervasives_Native.fst
                                                           (_split_subst_at_bv
                                                              (FStar_Pervasives_Native.__proj__Some__item__v
                                                                 shadowed_bv)
                                                              post_subst)
                                                       else post_subst))
                                                 (fun uu___2 ->
                                                    (fun pre_subst ->
                                                       Obj.magic
                                                         (FStar_Tactics_Effect.tac_bind
                                                            (FStar_Range.mk_range
                                                               "FStar.InteractiveHelpers.Output.fst"
                                                               (Prims.of_int (58))
                                                               (Prims.of_int (4))
                                                               (Prims.of_int (62))
                                                               (Prims.of_int (48)))
                                                            (FStar_Range.mk_range
                                                               "FStar.InteractiveHelpers.Output.fst"
                                                               (Prims.of_int (64))
                                                               (Prims.of_int (2))
                                                               (Prims.of_int (73))
                                                               (Prims.of_int (31)))
                                                            (FStar_Tactics_Effect.lift_div_tac
                                                               (fun uu___2 ->
                                                                  fun subst1
                                                                    ->
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Output.fst"
                                                                    (Prims.of_int (59))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (59))
                                                                    (Prims.of_int (63)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Output.fst"
                                                                    (Prims.of_int (61))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (62))
                                                                    (Prims.of_int (48)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    fun
                                                                    uu___4 ->
                                                                    match uu___4
                                                                    with
                                                                    | 
                                                                    ((x, ty),
                                                                    y) ->
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Output.fst"
                                                                    (Prims.of_int (59))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (59))
                                                                    (Prims.of_int (63)))
                                                                    (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (31)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Output.fst"
                                                                    (Prims.of_int (59))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (59))
                                                                    (Prims.of_int (27)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Output.fst"
                                                                    (Prims.of_int (59))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (59))
                                                                    (Prims.of_int (63)))
                                                                    (Obj.magic
                                                                    (FStar_InteractiveHelpers_Base.abv_to_string
                                                                    x))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Output.fst"
                                                                    (Prims.of_int (59))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (59))
                                                                    (Prims.of_int (63)))
                                                                    (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (31)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Output.fst"
                                                                    (Prims.of_int (59))
                                                                    (Prims.of_int (39))
                                                                    (Prims.of_int (59))
                                                                    (Prims.of_int (63)))
                                                                    (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (31)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Output.fst"
                                                                    (Prims.of_int (59))
                                                                    (Prims.of_int (39))
                                                                    (Prims.of_int (59))
                                                                    (Prims.of_int (55)))
                                                                    (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (31)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Builtins.term_to_string
                                                                    y))
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    Prims.strcat
                                                                    uu___6
                                                                    ")\n"))))
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    Prims.strcat
                                                                    " -> "
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
                                                                    "("
                                                                    uu___5))))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    to_string
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Output.fst"
                                                                    (Prims.of_int (61))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (61))
                                                                    (Prims.of_int (33)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Output.fst"
                                                                    (Prims.of_int (62))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (62))
                                                                    (Prims.of_int (48)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Util.map
                                                                    to_string
                                                                    subst1))
                                                                    (fun str
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_List_Tot_Base.fold_left
                                                                    (fun x ->
                                                                    fun y ->
                                                                    Prims.strcat
                                                                    x y) ""
                                                                    str))))
                                                                    uu___3)))
                                                            (fun uu___2 ->
                                                               (fun
                                                                  subst_to_string
                                                                  ->
                                                                  Obj.magic
                                                                    (
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Output.fst"
                                                                    (Prims.of_int (64))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (68))
                                                                    (Prims.of_int (7)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Output.fst"
                                                                    (Prims.of_int (70))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (73))
                                                                    (Prims.of_int (31)))
                                                                    (if dbg
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Output.fst"
                                                                    (Prims.of_int (66))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (66))
                                                                    (Prims.of_int (64)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Output.fst"
                                                                    (Prims.of_int (67))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (67))
                                                                    (Prims.of_int (66)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Output.fst"
                                                                    (Prims.of_int (66))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (66))
                                                                    (Prims.of_int (64)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Output.fst"
                                                                    (Prims.of_int (66))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (66))
                                                                    (Prims.of_int (64)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Output.fst"
                                                                    (Prims.of_int (66))
                                                                    (Prims.of_int (38))
                                                                    (Prims.of_int (66))
                                                                    (Prims.of_int (63)))
                                                                    (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (31)))
                                                                    (Obj.magic
                                                                    (subst_to_string
                                                                    pre_subst))
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    Prims.strcat
                                                                    "- pre_subst:\n"
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
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Output.fst"
                                                                    (Prims.of_int (67))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (67))
                                                                    (Prims.of_int (66)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Output.fst"
                                                                    (Prims.of_int (67))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (67))
                                                                    (Prims.of_int (66)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Output.fst"
                                                                    (Prims.of_int (67))
                                                                    (Prims.of_int (39))
                                                                    (Prims.of_int (67))
                                                                    (Prims.of_int (65)))
                                                                    (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (31)))
                                                                    (Obj.magic
                                                                    (subst_to_string
                                                                    post_subst))
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    Prims.strcat
                                                                    "- post_subst:\n"
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
                                                                    uu___2)))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    ()))))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    uu___2 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Output.fst"
                                                                    (Prims.of_int (70))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (70))
                                                                    (Prims.of_int (63)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Output.fst"
                                                                    (Prims.of_int (71))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (73))
                                                                    (Prims.of_int (31)))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    fun s ->
                                                                    FStar_Tactics_Util.map
                                                                    (fun t ->
                                                                    FStar_InteractiveHelpers_Base.apply_subst
                                                                    ge1.FStar_InteractiveHelpers_Base.env
                                                                    t s)))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    apply ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Output.fst"
                                                                    (Prims.of_int (71))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (71))
                                                                    (Prims.of_int (36)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Output.fst"
                                                                    (Prims.of_int (72))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (73))
                                                                    (Prims.of_int (31)))
                                                                    (Obj.magic
                                                                    (apply
                                                                    pre_subst
                                                                    es.FStar_InteractiveHelpers_Propositions.pres))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun pres
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Output.fst"
                                                                    (Prims.of_int (72))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (72))
                                                                    (Prims.of_int (39)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Output.fst"
                                                                    (Prims.of_int (73))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (73))
                                                                    (Prims.of_int (31)))
                                                                    (Obj.magic
                                                                    (apply
                                                                    post_subst
                                                                    es.FStar_InteractiveHelpers_Propositions.posts))
                                                                    (fun
                                                                    posts ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    (ge1,
                                                                    (FStar_InteractiveHelpers_Propositions.mk_assertions
                                                                    pres
                                                                    posts))))))
                                                                    uu___3)))
                                                                    uu___3)))
                                                                    uu___2)))
                                                                 uu___2)))
                                                      uu___2))) uu___2)))
                            uu___1))) uu___)
let (string_to_printout : Prims.string -> Prims.string -> Prims.string) =
  fun prefix ->
    fun data ->
      Prims.strcat prefix (Prims.strcat ":\n" (Prims.strcat data "\n"))
let (term_to_printout :
  FStar_InteractiveHelpers_Base.genv ->
    Prims.string ->
      FStar_Reflection_Types.term ->
        (Prims.string, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun ge ->
    fun prefix ->
      fun t ->
        FStar_Tactics_Effect.tac_bind
          (FStar_Range.mk_range "FStar.InteractiveHelpers.Output.fst"
             (Prims.of_int (87)) (Prims.of_int (12)) (Prims.of_int (87))
             (Prims.of_int (28)))
          (FStar_Range.mk_range "FStar.InteractiveHelpers.Output.fst"
             (Prims.of_int (88)) (Prims.of_int (2)) (Prims.of_int (92))
             (Prims.of_int (46)))
          (Obj.magic (FStar_InteractiveHelpers_ExploreTerm.abs_free_in ge t))
          (fun uu___ ->
             (fun abs ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Range.mk_range
                        "FStar.InteractiveHelpers.Output.fst"
                        (Prims.of_int (88)) (Prims.of_int (20))
                        (Prims.of_int (88)) (Prims.of_int (68)))
                     (FStar_Range.mk_range
                        "FStar.InteractiveHelpers.Output.fst"
                        (Prims.of_int (89)) (Prims.of_int (2))
                        (Prims.of_int (92)) (Prims.of_int (46)))
                     (FStar_Tactics_Effect.lift_div_tac
                        (fun uu___ ->
                           FStar_List_Tot_Base.map
                             (fun uu___1 ->
                                match uu___1 with
                                | (bv, t1) ->
                                    FStar_Reflection_Derived.mk_binder bv t1)
                             abs))
                     (fun uu___ ->
                        (fun abs_binders ->
                           Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Range.mk_range
                                   "FStar.InteractiveHelpers.Output.fst"
                                   (Prims.of_int (89)) (Prims.of_int (18))
                                   (Prims.of_int (89)) (Prims.of_int (59)))
                                (FStar_Range.mk_range
                                   "FStar.InteractiveHelpers.Output.fst"
                                   (Prims.of_int (90)) (Prims.of_int (2))
                                   (Prims.of_int (92)) (Prims.of_int (46)))
                                (Obj.magic
                                   (FStar_Tactics_Util.map
                                      (fun uu___ ->
                                         match uu___ with
                                         | (bv, uu___1) ->
                                             FStar_Tactics_Builtins.pack
                                               (FStar_Reflection_Data.Tv_Var
                                                  bv)) abs))
                                (fun uu___ ->
                                   (fun abs_terms ->
                                      Obj.magic
                                        (FStar_Tactics_Effect.tac_bind
                                           (FStar_Range.mk_range
                                              "FStar.InteractiveHelpers.Output.fst"
                                              (Prims.of_int (90))
                                              (Prims.of_int (10))
                                              (Prims.of_int (90))
                                              (Prims.of_int (30)))
                                           (FStar_Range.mk_range
                                              "FStar.InteractiveHelpers.Output.fst"
                                              (Prims.of_int (91))
                                              (Prims.of_int (2))
                                              (Prims.of_int (92))
                                              (Prims.of_int (46)))
                                           (Obj.magic
                                              (FStar_Tactics_Derived.mk_abs
                                                 abs_binders t))
                                           (fun uu___ ->
                                              (fun t1 ->
                                                 Obj.magic
                                                   (FStar_Tactics_Effect.tac_bind
                                                      (FStar_Range.mk_range
                                                         "FStar.InteractiveHelpers.Output.fst"
                                                         (Prims.of_int (91))
                                                         (Prims.of_int (10))
                                                         (Prims.of_int (91))
                                                         (Prims.of_int (30)))
                                                      (FStar_Range.mk_range
                                                         "FStar.InteractiveHelpers.Output.fst"
                                                         (Prims.of_int (92))
                                                         (Prims.of_int (2))
                                                         (Prims.of_int (92))
                                                         (Prims.of_int (46)))
                                                      (FStar_Tactics_Effect.lift_div_tac
                                                         (fun uu___ ->
                                                            FStar_Reflection_Derived.mk_e_app
                                                              t1 abs_terms))
                                                      (fun uu___ ->
                                                         (fun t2 ->
                                                            Obj.magic
                                                              (FStar_Tactics_Effect.tac_bind
                                                                 (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Output.fst"
                                                                    (Prims.of_int (92))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (92))
                                                                    (Prims.of_int (46)))
                                                                 (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Output.fst"
                                                                    (Prims.of_int (92))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (92))
                                                                    (Prims.of_int (46)))
                                                                 (Obj.magic
                                                                    (
                                                                    FStar_Tactics_Builtins.term_to_string
                                                                    t2))
                                                                 (fun uu___
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___1 ->
                                                                    string_to_printout
                                                                    prefix
                                                                    uu___))))
                                                           uu___))) uu___)))
                                     uu___))) uu___))) uu___)
let (opt_term_to_printout :
  FStar_InteractiveHelpers_Base.genv ->
    Prims.string ->
      FStar_Reflection_Types.term FStar_Pervasives_Native.option ->
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
        FStar_Tactics_Effect.tac_bind
          (FStar_Range.mk_range "FStar.InteractiveHelpers.Output.fst"
             (Prims.of_int (104)) (Prims.of_int (4)) (Prims.of_int (105))
             (Prims.of_int (40)))
          (FStar_Range.mk_range "FStar.InteractiveHelpers.Output.fst"
             (Prims.of_int (107)) (Prims.of_int (2)) (Prims.of_int (113))
             (Prims.of_int (5)))
          (FStar_Tactics_Effect.lift_div_tac
             (fun uu___ ->
                fun i ->
                  fun p ->
                    FStar_Tactics_Effect.tac_bind
                      (FStar_Range.mk_range
                         "FStar.InteractiveHelpers.Output.fst"
                         (Prims.of_int (104)) (Prims.of_int (18))
                         (Prims.of_int (104)) (Prims.of_int (52)))
                      (FStar_Range.mk_range
                         "FStar.InteractiveHelpers.Output.fst"
                         (Prims.of_int (105)) (Prims.of_int (4))
                         (Prims.of_int (105)) (Prims.of_int (40)))
                      (FStar_Tactics_Effect.lift_div_tac
                         (fun uu___1 ->
                            Prims.strcat prefix
                              (Prims.strcat ":prop" (Prims.string_of_int i))))
                      (fun uu___1 ->
                         (fun prefix' ->
                            Obj.magic (proposition_to_printout ge prefix' p))
                           uu___1)))
          (fun uu___ ->
             (fun prop_to_printout ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Range.mk_range
                        "FStar.InteractiveHelpers.Output.fst"
                        (Prims.of_int (107)) (Prims.of_int (12))
                        (Prims.of_int (107)) (Prims.of_int (85)))
                     (FStar_Range.mk_range
                        "FStar.InteractiveHelpers.Output.fst"
                        (Prims.of_int (108)) (Prims.of_int (2))
                        (Prims.of_int (113)) (Prims.of_int (5)))
                     (FStar_Tactics_Effect.lift_div_tac
                        (fun uu___ ->
                           string_to_printout (Prims.strcat prefix ":num")
                             (Prims.string_of_int
                                (FStar_List_Tot_Base.length pl))))
                     (fun uu___ ->
                        (fun str ->
                           Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Range.mk_range
                                   "FStar.InteractiveHelpers.Output.fst"
                                   (Prims.of_int (109)) (Prims.of_int (4))
                                   (Prims.of_int (110)) (Prims.of_int (33)))
                                (FStar_Range.mk_range
                                   "FStar.InteractiveHelpers.Output.fst"
                                   (Prims.of_int (112)) (Prims.of_int (2))
                                   (Prims.of_int (113)) (Prims.of_int (5)))
                                (FStar_Tactics_Effect.lift_div_tac
                                   (fun uu___ ->
                                      fun s_i ->
                                        fun p ->
                                          FStar_Tactics_Effect.tac_bind
                                            (FStar_Range.mk_range
                                               "FStar.InteractiveHelpers.Output.fst"
                                               (Prims.of_int (109))
                                               (Prims.of_int (15))
                                               (Prims.of_int (109))
                                               (Prims.of_int (18)))
                                            (FStar_Range.mk_range
                                               "FStar.InteractiveHelpers.Output.fst"
                                               (Prims.of_int (109))
                                               (Prims.of_int (4))
                                               (Prims.of_int (110))
                                               (Prims.of_int (33)))
                                            (FStar_Tactics_Effect.lift_div_tac
                                               (fun uu___1 -> s_i))
                                            (fun uu___1 ->
                                               (fun uu___1 ->
                                                  match uu___1 with
                                                  | (s, i) ->
                                                      Obj.magic
                                                        (FStar_Tactics_Effect.tac_bind
                                                           (FStar_Range.mk_range
                                                              "FStar.InteractiveHelpers.Output.fst"
                                                              (Prims.of_int (110))
                                                              (Prims.of_int (4))
                                                              (Prims.of_int (110))
                                                              (Prims.of_int (28)))
                                                           (FStar_Range.mk_range
                                                              "FStar.InteractiveHelpers.Output.fst"
                                                              (Prims.of_int (110))
                                                              (Prims.of_int (4))
                                                              (Prims.of_int (110))
                                                              (Prims.of_int (33)))
                                                           (Obj.magic
                                                              (FStar_Tactics_Effect.tac_bind
                                                                 (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Output.fst"
                                                                    (Prims.of_int (110))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (110))
                                                                    (Prims.of_int (28)))
                                                                 (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (31)))
                                                                 (Obj.magic
                                                                    (
                                                                    prop_to_printout
                                                                    i p))
                                                                 (fun uu___2
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    Prims.strcat
                                                                    s uu___2))))
                                                           (fun uu___2 ->
                                                              FStar_Tactics_Effect.lift_div_tac
                                                                (fun uu___3
                                                                   ->
                                                                   (uu___2,
                                                                    (i +
                                                                    Prims.int_one))))))
                                                 uu___1)))
                                (fun uu___ ->
                                   (fun concat_prop ->
                                      Obj.magic
                                        (FStar_Tactics_Effect.tac_bind
                                           (FStar_Range.mk_range
                                              "FStar.InteractiveHelpers.Output.fst"
                                              (Prims.of_int (112))
                                              (Prims.of_int (15))
                                              (Prims.of_int (112))
                                              (Prims.of_int (47)))
                                           (FStar_Range.mk_range
                                              "FStar.InteractiveHelpers.Output.fst"
                                              (Prims.of_int (112))
                                              (Prims.of_int (2))
                                              (Prims.of_int (113))
                                              (Prims.of_int (5)))
                                           (Obj.magic
                                              (FStar_Tactics_Util.fold_left
                                                 concat_prop
                                                 (str, Prims.int_zero) pl))
                                           (fun uu___ ->
                                              FStar_Tactics_Effect.lift_div_tac
                                                (fun uu___1 ->
                                                   match uu___ with
                                                   | (str1, uu___2) -> str1))))
                                     uu___))) uu___))) uu___)
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
      FStar_Tactics_Effect.tac_bind
        (FStar_Range.mk_range "FStar.InteractiveHelpers.Output.fst"
           (Prims.of_int (126)) (Prims.of_int (12)) (Prims.of_int (126))
           (Prims.of_int (31)))
        (FStar_Range.mk_range "FStar.InteractiveHelpers.Output.fst"
           (Prims.of_int (130)) (Prims.of_int (2)) (Prims.of_int (142))
           (Prims.of_int (50)))
        (FStar_Tactics_Effect.lift_div_tac
           (fun uu___ -> Prims.strcat prefix ":BEGIN\n"))
        (fun uu___ ->
           (fun str ->
              Obj.magic
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Range.mk_range
                      "FStar.InteractiveHelpers.Output.fst"
                      (Prims.of_int (131)) (Prims.of_int (4))
                      (Prims.of_int (135)) (Prims.of_int (26)))
                   (FStar_Range.mk_range
                      "FStar.InteractiveHelpers.Output.fst"
                      (Prims.of_int (130)) (Prims.of_int (2))
                      (Prims.of_int (142)) (Prims.of_int (50)))
                   (match res with
                    | ESuccess (ge, a) ->
                        Obj.magic
                          (Obj.repr
                             (FStar_Tactics_Effect.lift_div_tac
                                (fun uu___ ->
                                   (FStar_Pervasives_Native.None, ge,
                                     (a.FStar_InteractiveHelpers_Propositions.pres),
                                     (a.FStar_InteractiveHelpers_Propositions.posts)))))
                    | EFailure err ->
                        Obj.magic
                          (Obj.repr
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Range.mk_range
                                   "FStar.InteractiveHelpers.Output.fst"
                                   (Prims.of_int (134)) (Prims.of_int (15))
                                   (Prims.of_int (134)) (Prims.of_int (40)))
                                (FStar_Range.mk_range
                                   "FStar.InteractiveHelpers.Output.fst"
                                   (Prims.of_int (135)) (Prims.of_int (6))
                                   (Prims.of_int (135)) (Prims.of_int (26)))
                                (Obj.magic
                                   (FStar_Tactics_Effect.tac_bind
                                      (FStar_Range.mk_range
                                         "FStar.InteractiveHelpers.Output.fst"
                                         (Prims.of_int (134))
                                         (Prims.of_int (28))
                                         (Prims.of_int (134))
                                         (Prims.of_int (40)))
                                      (FStar_Range.mk_range
                                         "FStar.InteractiveHelpers.Output.fst"
                                         (Prims.of_int (134))
                                         (Prims.of_int (15))
                                         (Prims.of_int (134))
                                         (Prims.of_int (40)))
                                      (Obj.magic
                                         (FStar_Tactics_Builtins.top_env ()))
                                      (fun uu___ ->
                                         FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___1 ->
                                              FStar_InteractiveHelpers_Base.mk_init_genv
                                                uu___))))
                                (fun ge ->
                                   FStar_Tactics_Effect.lift_div_tac
                                     (fun uu___ ->
                                        ((FStar_Pervasives_Native.Some err),
                                          ge, [], []))))))
                   (fun uu___ ->
                      (fun uu___ ->
                         match uu___ with
                         | (err, ge, pres, posts) ->
                             Obj.magic
                               (FStar_Tactics_Effect.tac_bind
                                  (FStar_Range.mk_range
                                     "FStar.InteractiveHelpers.Output.fst"
                                     (Prims.of_int (138)) (Prims.of_int (12))
                                     (Prims.of_int (138)) (Prims.of_int (54)))
                                  (FStar_Range.mk_range
                                     "FStar.InteractiveHelpers.Output.fst"
                                     (Prims.of_int (140)) (Prims.of_int (2))
                                     (Prims.of_int (142)) (Prims.of_int (50)))
                                  (FStar_Tactics_Effect.lift_div_tac
                                     (fun uu___1 ->
                                        Prims.strcat str
                                          (error_message_to_printout prefix
                                             err)))
                                  (fun uu___1 ->
                                     (fun str1 ->
                                        Obj.magic
                                          (FStar_Tactics_Effect.tac_bind
                                             (FStar_Range.mk_range
                                                "FStar.InteractiveHelpers.Output.fst"
                                                (Prims.of_int (140))
                                                (Prims.of_int (12))
                                                (Prims.of_int (140))
                                                (Prims.of_int (69)))
                                             (FStar_Range.mk_range
                                                "FStar.InteractiveHelpers.Output.fst"
                                                (Prims.of_int (141))
                                                (Prims.of_int (2))
                                                (Prims.of_int (142))
                                                (Prims.of_int (50)))
                                             (Obj.magic
                                                (FStar_Tactics_Effect.tac_bind
                                                   (FStar_Range.mk_range
                                                      "FStar.InteractiveHelpers.Output.fst"
                                                      (Prims.of_int (140))
                                                      (Prims.of_int (18))
                                                      (Prims.of_int (140))
                                                      (Prims.of_int (69)))
                                                   (FStar_Range.mk_range
                                                      "prims.fst"
                                                      (Prims.of_int (590))
                                                      (Prims.of_int (19))
                                                      (Prims.of_int (590))
                                                      (Prims.of_int (31)))
                                                   (Obj.magic
                                                      (propositions_to_printout
                                                         ge
                                                         (Prims.strcat prefix
                                                            ":pres") pres))
                                                   (fun uu___1 ->
                                                      FStar_Tactics_Effect.lift_div_tac
                                                        (fun uu___2 ->
                                                           Prims.strcat str1
                                                             uu___1))))
                                             (fun uu___1 ->
                                                (fun str2 ->
                                                   Obj.magic
                                                     (FStar_Tactics_Effect.tac_bind
                                                        (FStar_Range.mk_range
                                                           "FStar.InteractiveHelpers.Output.fst"
                                                           (Prims.of_int (141))
                                                           (Prims.of_int (12))
                                                           (Prims.of_int (141))
                                                           (Prims.of_int (71)))
                                                        (FStar_Range.mk_range
                                                           "prims.fst"
                                                           (Prims.of_int (590))
                                                           (Prims.of_int (19))
                                                           (Prims.of_int (590))
                                                           (Prims.of_int (31)))
                                                        (Obj.magic
                                                           (FStar_Tactics_Effect.tac_bind
                                                              (FStar_Range.mk_range
                                                                 "FStar.InteractiveHelpers.Output.fst"
                                                                 (Prims.of_int (141))
                                                                 (Prims.of_int (18))
                                                                 (Prims.of_int (141))
                                                                 (Prims.of_int (71)))
                                                              (FStar_Range.mk_range
                                                                 "prims.fst"
                                                                 (Prims.of_int (590))
                                                                 (Prims.of_int (19))
                                                                 (Prims.of_int (590))
                                                                 (Prims.of_int (31)))
                                                              (Obj.magic
                                                                 (propositions_to_printout
                                                                    ge
                                                                    (
                                                                    Prims.strcat
                                                                    prefix
                                                                    ":posts")
                                                                    posts))
                                                              (fun uu___1 ->
                                                                 FStar_Tactics_Effect.lift_div_tac
                                                                   (fun
                                                                    uu___2 ->
                                                                    Prims.strcat
                                                                    str2
                                                                    uu___1))))
                                                        (fun str3 ->
                                                           FStar_Tactics_Effect.lift_div_tac
                                                             (fun uu___1 ->
                                                                Prims.strcat
                                                                  str3
                                                                  (Prims.strcat
                                                                    prefix
                                                                    ":END\n%FIH:FSTAR_META:END%")))))
                                                  uu___1))) uu___1))) uu___)))
             uu___)
let (printout_result :
  Prims.string -> export_result -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun prefix ->
    fun res ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Range.mk_range "FStar.InteractiveHelpers.Output.fst"
           (Prims.of_int (146)) (Prims.of_int (8)) (Prims.of_int (146))
           (Prims.of_int (39)))
        (FStar_Range.mk_range "FStar.InteractiveHelpers.Output.fst"
           (Prims.of_int (146)) (Prims.of_int (2)) (Prims.of_int (146))
           (Prims.of_int (39))) (Obj.magic (result_to_printout prefix res))
        (fun uu___ ->
           (fun uu___ -> Obj.magic (FStar_Tactics_Builtins.print uu___))
             uu___)
let (printout_success :
  FStar_InteractiveHelpers_Base.genv ->
    FStar_InteractiveHelpers_Propositions.assertions ->
      (unit, unit) FStar_Tactics_Effect.tac_repr)
  = fun ge -> fun a -> printout_result "ainfo" (ESuccess (ge, a))
let (printout_failure :
  Prims.string -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun err -> printout_result "ainfo" (EFailure err)
let (_debug_print_var :
  Prims.string ->
    FStar_Reflection_Types.term -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun name ->
    fun t ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Range.mk_range "FStar.InteractiveHelpers.Output.fst"
           (Prims.of_int (157)) (Prims.of_int (2)) (Prims.of_int (157))
           (Prims.of_int (63)))
        (FStar_Range.mk_range "FStar.InteractiveHelpers.Output.fst"
           (Prims.of_int (158)) (Prims.of_int (2)) (Prims.of_int (170))
           (Prims.of_int (33)))
        (Obj.magic
           (FStar_Tactics_Effect.tac_bind
              (FStar_Range.mk_range "FStar.InteractiveHelpers.Output.fst"
                 (Prims.of_int (157)) (Prims.of_int (8)) (Prims.of_int (157))
                 (Prims.of_int (63)))
              (FStar_Range.mk_range "FStar.InteractiveHelpers.Output.fst"
                 (Prims.of_int (157)) (Prims.of_int (2)) (Prims.of_int (157))
                 (Prims.of_int (63)))
              (Obj.magic
                 (FStar_Tactics_Effect.tac_bind
                    (FStar_Range.mk_range
                       "FStar.InteractiveHelpers.Output.fst"
                       (Prims.of_int (157)) (Prims.of_int (32))
                       (Prims.of_int (157)) (Prims.of_int (62)))
                    (FStar_Range.mk_range "prims.fst" (Prims.of_int (590))
                       (Prims.of_int (19)) (Prims.of_int (590))
                       (Prims.of_int (31)))
                    (Obj.magic
                       (FStar_Tactics_Effect.tac_bind
                          (FStar_Range.mk_range
                             "FStar.InteractiveHelpers.Output.fst"
                             (Prims.of_int (157)) (Prims.of_int (39))
                             (Prims.of_int (157)) (Prims.of_int (62)))
                          (FStar_Range.mk_range "prims.fst"
                             (Prims.of_int (590)) (Prims.of_int (19))
                             (Prims.of_int (590)) (Prims.of_int (31)))
                          (Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Range.mk_range
                                   "FStar.InteractiveHelpers.Output.fst"
                                   (Prims.of_int (157)) (Prims.of_int (46))
                                   (Prims.of_int (157)) (Prims.of_int (62)))
                                (FStar_Range.mk_range "prims.fst"
                                   (Prims.of_int (590)) (Prims.of_int (19))
                                   (Prims.of_int (590)) (Prims.of_int (31)))
                                (Obj.magic
                                   (FStar_Tactics_Builtins.term_to_string t))
                                (fun uu___ ->
                                   FStar_Tactics_Effect.lift_div_tac
                                     (fun uu___1 -> Prims.strcat ": " uu___))))
                          (fun uu___ ->
                             FStar_Tactics_Effect.lift_div_tac
                               (fun uu___1 -> Prims.strcat name uu___))))
                    (fun uu___ ->
                       FStar_Tactics_Effect.lift_div_tac
                         (fun uu___1 ->
                            Prims.strcat "_debug_print_var: " uu___))))
              (fun uu___ ->
                 (fun uu___ -> Obj.magic (FStar_Tactics_Builtins.print uu___))
                   uu___)))
        (fun uu___ ->
           (fun uu___ ->
              Obj.magic
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Range.mk_range
                      "FStar.InteractiveHelpers.Output.fst"
                      (Prims.of_int (158)) (Prims.of_int (8))
                      (Prims.of_int (160)) (Prims.of_int (11)))
                   (FStar_Range.mk_range
                      "FStar.InteractiveHelpers.Output.fst"
                      (Prims.of_int (162)) (Prims.of_int (2))
                      (Prims.of_int (170)) (Prims.of_int (33)))
                   (Obj.magic
                      (FStar_Tactics_Effect.tac_bind
                         (FStar_Range.mk_range
                            "FStar.InteractiveHelpers.Output.fst"
                            (Prims.of_int (158)) (Prims.of_int (14))
                            (Prims.of_int (158)) (Prims.of_int (36)))
                         (FStar_Range.mk_range
                            "FStar.InteractiveHelpers.Output.fst"
                            (Prims.of_int (158)) (Prims.of_int (8))
                            (Prims.of_int (160)) (Prims.of_int (11)))
                         (Obj.magic
                            (FStar_Tactics_Effect.tac_bind
                               (FStar_Range.mk_range
                                  "FStar.InteractiveHelpers.Output.fst"
                                  (Prims.of_int (158)) (Prims.of_int (22))
                                  (Prims.of_int (158)) (Prims.of_int (34)))
                               (FStar_Range.mk_range
                                  "FStar.InteractiveHelpers.Output.fst"
                                  (Prims.of_int (158)) (Prims.of_int (14))
                                  (Prims.of_int (158)) (Prims.of_int (36)))
                               (Obj.magic (FStar_Tactics_Builtins.top_env ()))
                               (fun uu___1 ->
                                  (fun uu___1 ->
                                     Obj.magic
                                       (FStar_InteractiveHelpers_ExploreTerm.safe_tc
                                          uu___1 t)) uu___1)))
                         (fun uu___1 ->
                            (fun uu___1 ->
                               match uu___1 with
                               | FStar_Pervasives_Native.Some ty ->
                                   Obj.magic
                                     (Obj.repr
                                        (FStar_Tactics_Effect.tac_bind
                                           (FStar_Range.mk_range
                                              "FStar.InteractiveHelpers.Output.fst"
                                              (Prims.of_int (159))
                                              (Prims.of_int (21))
                                              (Prims.of_int (159))
                                              (Prims.of_int (51)))
                                           (FStar_Range.mk_range
                                              "FStar.InteractiveHelpers.Output.fst"
                                              (Prims.of_int (159))
                                              (Prims.of_int (15))
                                              (Prims.of_int (159))
                                              (Prims.of_int (51)))
                                           (Obj.magic
                                              (FStar_Tactics_Effect.tac_bind
                                                 (FStar_Range.mk_range
                                                    "FStar.InteractiveHelpers.Output.fst"
                                                    (Prims.of_int (159))
                                                    (Prims.of_int (33))
                                                    (Prims.of_int (159))
                                                    (Prims.of_int (50)))
                                                 (FStar_Range.mk_range
                                                    "prims.fst"
                                                    (Prims.of_int (590))
                                                    (Prims.of_int (19))
                                                    (Prims.of_int (590))
                                                    (Prims.of_int (31)))
                                                 (Obj.magic
                                                    (FStar_Tactics_Builtins.term_to_string
                                                       ty))
                                                 (fun uu___2 ->
                                                    FStar_Tactics_Effect.lift_div_tac
                                                      (fun uu___3 ->
                                                         Prims.strcat
                                                           "type: " uu___2))))
                                           (fun uu___2 ->
                                              (fun uu___2 ->
                                                 Obj.magic
                                                   (FStar_Tactics_Builtins.print
                                                      uu___2)) uu___2)))
                               | uu___2 ->
                                   Obj.magic
                                     (Obj.repr
                                        (FStar_Tactics_Effect.lift_div_tac
                                           (fun uu___3 -> ())))) uu___1)))
                   (fun uu___1 ->
                      (fun uu___1 ->
                         Obj.magic
                           (FStar_Tactics_Effect.tac_bind
                              (FStar_Range.mk_range
                                 "FStar.InteractiveHelpers.Output.fst"
                                 (Prims.of_int (162)) (Prims.of_int (2))
                                 (Prims.of_int (162)) (Prims.of_int (42)))
                              (FStar_Range.mk_range
                                 "FStar.InteractiveHelpers.Output.fst"
                                 (Prims.of_int (163)) (Prims.of_int (2))
                                 (Prims.of_int (170)) (Prims.of_int (33)))
                              (Obj.magic
                                 (FStar_Tactics_Effect.tac_bind
                                    (FStar_Range.mk_range
                                       "FStar.InteractiveHelpers.Output.fst"
                                       (Prims.of_int (162))
                                       (Prims.of_int (8))
                                       (Prims.of_int (162))
                                       (Prims.of_int (42)))
                                    (FStar_Range.mk_range
                                       "FStar.InteractiveHelpers.Output.fst"
                                       (Prims.of_int (162))
                                       (Prims.of_int (2))
                                       (Prims.of_int (162))
                                       (Prims.of_int (42)))
                                    (Obj.magic
                                       (FStar_Tactics_Effect.tac_bind
                                          (FStar_Range.mk_range
                                             "FStar.InteractiveHelpers.Output.fst"
                                             (Prims.of_int (162))
                                             (Prims.of_int (25))
                                             (Prims.of_int (162))
                                             (Prims.of_int (41)))
                                          (FStar_Range.mk_range "prims.fst"
                                             (Prims.of_int (590))
                                             (Prims.of_int (19))
                                             (Prims.of_int (590))
                                             (Prims.of_int (31)))
                                          (Obj.magic
                                             (FStar_InteractiveHelpers_Base.term_construct
                                                t))
                                          (fun uu___2 ->
                                             FStar_Tactics_Effect.lift_div_tac
                                               (fun uu___3 ->
                                                  Prims.strcat "qualifier: "
                                                    uu___2))))
                                    (fun uu___2 ->
                                       (fun uu___2 ->
                                          Obj.magic
                                            (FStar_Tactics_Builtins.print
                                               uu___2)) uu___2)))
                              (fun uu___2 ->
                                 (fun uu___2 ->
                                    Obj.magic
                                      (FStar_Tactics_Effect.tac_bind
                                         (FStar_Range.mk_range
                                            "FStar.InteractiveHelpers.Output.fst"
                                            (Prims.of_int (163))
                                            (Prims.of_int (8))
                                            (Prims.of_int (168))
                                            (Prims.of_int (11)))
                                         (FStar_Range.mk_range
                                            "FStar.InteractiveHelpers.Output.fst"
                                            (Prims.of_int (170))
                                            (Prims.of_int (2))
                                            (Prims.of_int (170))
                                            (Prims.of_int (33)))
                                         (Obj.magic
                                            (FStar_Tactics_Effect.tac_bind
                                               (FStar_Range.mk_range
                                                  "FStar.InteractiveHelpers.Output.fst"
                                                  (Prims.of_int (163))
                                                  (Prims.of_int (14))
                                                  (Prims.of_int (163))
                                                  (Prims.of_int (23)))
                                               (FStar_Range.mk_range
                                                  "FStar.InteractiveHelpers.Output.fst"
                                                  (Prims.of_int (163))
                                                  (Prims.of_int (8))
                                                  (Prims.of_int (168))
                                                  (Prims.of_int (11)))
                                               (Obj.magic
                                                  (FStar_Tactics_Builtins.inspect
                                                     t))
                                               (fun uu___3 ->
                                                  (fun uu___3 ->
                                                     match uu___3 with
                                                     | FStar_Reflection_Data.Tv_Var
                                                         bv ->
                                                         Obj.magic
                                                           (Obj.repr
                                                              (FStar_Tactics_Effect.tac_bind
                                                                 (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Output.fst"
                                                                    (Prims.of_int (165))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (165))
                                                                    (Prims.of_int (35)))
                                                                 (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Output.fst"
                                                                    (Prims.of_int (166))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (167))
                                                                    (Prims.of_int (52)))
                                                                 (FStar_Tactics_Effect.lift_div_tac
                                                                    (
                                                                    fun
                                                                    uu___4 ->
                                                                    FStar_Reflection_Builtins.inspect_bv
                                                                    bv))
                                                                 (fun uu___4
                                                                    ->
                                                                    (fun b ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Output.fst"
                                                                    (Prims.of_int (166))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (167))
                                                                    (Prims.of_int (52)))
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Output.fst"
                                                                    (Prims.of_int (166))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (167))
                                                                    (Prims.of_int (52)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Range.mk_range
                                                                    "FStar.InteractiveHelpers.Output.fst"
                                                                    (Prims.of_int (166))
                                                                    (Prims.of_int (32))
                                                                    (Prims.of_int (167))
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
                                                                    "FStar.InteractiveHelpers.Output.fst"
                                                                    (Prims.of_int (166))
                                                                    (Prims.of_int (32))
                                                                    (Prims.of_int (166))
                                                                    (Prims.of_int (45)))
                                                                    (FStar_Range.mk_range
                                                                    "prims.fst"
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (590))
                                                                    (Prims.of_int (31)))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Derived.name_of_bv
                                                                    bv))
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    Prims.strcat
                                                                    uu___4
                                                                    (Prims.strcat
                                                                    "; index: "
                                                                    (Prims.string_of_int
                                                                    b.FStar_Reflection_Data.bv_index))))))
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    Prims.strcat
                                                                    "Tv_Var: ppname: "
                                                                    uu___4))))
                                                                    (fun
                                                                    uu___4 ->
                                                                    (fun
                                                                    uu___4 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Builtins.print
                                                                    uu___4))
                                                                    uu___4)))
                                                                    uu___4)))
                                                     | uu___4 ->
                                                         Obj.magic
                                                           (Obj.repr
                                                              (FStar_Tactics_Effect.lift_div_tac
                                                                 (fun uu___5
                                                                    -> ()))))
                                                    uu___3)))
                                         (fun uu___3 ->
                                            (fun uu___3 ->
                                               Obj.magic
                                                 (FStar_Tactics_Builtins.print
                                                    "end of _debug_print_var"))
                                              uu___3))) uu___2))) uu___1)))
             uu___)
let magic_witness : 'a . unit -> 'a =
  fun uu___ -> failwith "Not yet implemented:magic_witness"
let (tadmit_no_warning : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___ ->
    FStar_Tactics_Derived.apply
      (FStar_Reflection_Builtins.pack_ln
         (FStar_Reflection_Data.Tv_FVar
            (FStar_Reflection_Builtins.pack_fv
               ["FStar"; "InteractiveHelpers"; "Output"; "magic_witness"])))
let (pp_tac : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Range.mk_range "FStar.InteractiveHelpers.Output.fst"
         (Prims.of_int (184)) (Prims.of_int (2)) (Prims.of_int (184))
         (Prims.of_int (62)))
      (FStar_Range.mk_range "FStar.InteractiveHelpers.Output.fst"
         (Prims.of_int (185)) (Prims.of_int (2)) (Prims.of_int (186))
         (Prims.of_int (9)))
      (Obj.magic
         (FStar_Tactics_Effect.tac_bind
            (FStar_Range.mk_range "FStar.InteractiveHelpers.Output.fst"
               (Prims.of_int (184)) (Prims.of_int (8)) (Prims.of_int (184))
               (Prims.of_int (62)))
            (FStar_Range.mk_range "FStar.InteractiveHelpers.Output.fst"
               (Prims.of_int (184)) (Prims.of_int (2)) (Prims.of_int (184))
               (Prims.of_int (62)))
            (Obj.magic
               (FStar_Tactics_Effect.tac_bind
                  (FStar_Range.mk_range "FStar.InteractiveHelpers.Output.fst"
                     (Prims.of_int (184)) (Prims.of_int (31))
                     (Prims.of_int (184)) (Prims.of_int (61)))
                  (FStar_Range.mk_range "prims.fst" (Prims.of_int (590))
                     (Prims.of_int (19)) (Prims.of_int (590))
                     (Prims.of_int (31)))
                  (Obj.magic
                     (FStar_Tactics_Effect.tac_bind
                        (FStar_Range.mk_range
                           "FStar.InteractiveHelpers.Output.fst"
                           (Prims.of_int (184)) (Prims.of_int (47))
                           (Prims.of_int (184)) (Prims.of_int (60)))
                        (FStar_Range.mk_range
                           "FStar.InteractiveHelpers.Output.fst"
                           (Prims.of_int (184)) (Prims.of_int (31))
                           (Prims.of_int (184)) (Prims.of_int (61)))
                        (Obj.magic (FStar_Tactics_Derived.cur_goal ()))
                        (fun uu___1 ->
                           (fun uu___1 ->
                              Obj.magic
                                (FStar_Tactics_Builtins.term_to_string uu___1))
                             uu___1)))
                  (fun uu___1 ->
                     FStar_Tactics_Effect.lift_div_tac
                       (fun uu___2 -> Prims.strcat "post-processing: " uu___1))))
            (fun uu___1 ->
               (fun uu___1 -> Obj.magic (FStar_Tactics_Builtins.print uu___1))
                 uu___1)))
      (fun uu___1 ->
         (fun uu___1 ->
            Obj.magic
              (FStar_Tactics_Effect.tac_bind
                 (FStar_Range.mk_range "FStar.InteractiveHelpers.Output.fst"
                    (Prims.of_int (185)) (Prims.of_int (2))
                    (Prims.of_int (185)) (Prims.of_int (9)))
                 (FStar_Range.mk_range "FStar.InteractiveHelpers.Output.fst"
                    (Prims.of_int (186)) (Prims.of_int (2))
                    (Prims.of_int (186)) (Prims.of_int (9)))
                 (Obj.magic (FStar_Tactics_Builtins.dump ""))
                 (fun uu___2 ->
                    (fun uu___2 -> Obj.magic (FStar_Tactics_Derived.trefl ()))
                      uu___2))) uu___1)
