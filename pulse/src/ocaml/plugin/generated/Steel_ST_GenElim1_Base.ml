open Prims
let (is_fvar : FStar_Reflection_Types.term -> Prims.string -> Prims.bool) =
  FStar_Reflection_V1_Derived.is_fvar
let (is_any_fvar :
  FStar_Reflection_Types.term -> Prims.string Prims.list -> Prims.bool) =
  FStar_Reflection_V1_Derived.is_any_fvar
let (is_squash :
  FStar_Reflection_Types.term ->
    (Prims.bool, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___ ->
    (fun t ->
       Obj.magic
         (FStar_Tactics_Effect.lift_div_tac
            (fun uu___ -> is_any_fvar t ["Prims.squash"; "Prims.auto_squash"])))
      uu___
let (is_star_or_vstar :
  FStar_Reflection_Types.term ->
    (Prims.bool, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___ ->
    (fun t ->
       Obj.magic
         (FStar_Tactics_Effect.lift_div_tac
            (fun uu___ ->
               is_any_fvar t
                 ["Steel.Effect.Common.star"; "Steel.Effect.Common.VStar"])))
      uu___
let rec (term_has_head :
  FStar_Reflection_Types.term ->
    FStar_Reflection_Types.term ->
      (Prims.bool, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    fun head ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Steel.ST.GenElim1.Base.fsti"
                 (Prims.of_int (341)) (Prims.of_int (17))
                 (Prims.of_int (341)) (Prims.of_int (32)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Steel.ST.GenElim1.Base.fsti"
                 (Prims.of_int (341)) Prims.int_one (Prims.of_int (352))
                 (Prims.of_int (12)))))
        (Obj.magic (FStar_Tactics_V1_SyntaxHelpers.collect_app t))
        (fun uu___ ->
           (fun uu___ ->
              match uu___ with
              | (hd, tl) ->
                  Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "Steel.ST.GenElim1.Base.fsti"
                                (Prims.of_int (342)) (Prims.of_int (5))
                                (Prims.of_int (342)) (Prims.of_int (28)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "Steel.ST.GenElim1.Base.fsti"
                                (Prims.of_int (342)) (Prims.of_int (2))
                                (Prims.of_int (352)) (Prims.of_int (12)))))
                       (Obj.magic
                          (FStar_Tactics_V1_Builtins.term_eq_old hd head))
                       (fun uu___1 ->
                          (fun uu___1 ->
                             if uu___1
                             then
                               Obj.magic
                                 (Obj.repr
                                    (FStar_Tactics_Effect.lift_div_tac
                                       (fun uu___2 -> true)))
                             else
                               Obj.magic
                                 (Obj.repr
                                    (FStar_Tactics_Effect.tac_bind
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "Steel.ST.GenElim1.Base.fsti"
                                                (Prims.of_int (344))
                                                (Prims.of_int (10))
                                                (Prims.of_int (344))
                                                (Prims.of_int (29)))))
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "Steel.ST.GenElim1.Base.fsti"
                                                (Prims.of_int (344))
                                                (Prims.of_int (7))
                                                (Prims.of_int (352))
                                                (Prims.of_int (12)))))
                                       (Obj.magic (is_star_or_vstar hd))
                                       (fun uu___3 ->
                                          (fun uu___3 ->
                                             if uu___3
                                             then
                                               Obj.magic
                                                 (Obj.repr
                                                    (match tl with
                                                     | (tg,
                                                        FStar_Reflection_V1_Data.Q_Explicit)::
                                                         (td,
                                                          FStar_Reflection_V1_Data.Q_Explicit)::[]
                                                         ->
                                                         Obj.repr
                                                           (FStar_Tactics_Effect.tac_bind
                                                              (FStar_Sealed.seal
                                                                 (Obj.magic
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (348))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (348))
                                                                    (Prims.of_int (30)))))
                                                              (FStar_Sealed.seal
                                                                 (Obj.magic
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (348))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (350))
                                                                    (Prims.of_int (32)))))
                                                              (Obj.magic
                                                                 (term_has_head
                                                                    tg head))
                                                              (fun uu___4 ->
                                                                 (fun uu___4
                                                                    ->
                                                                    if uu___4
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    true)))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (term_has_head
                                                                    td head)))
                                                                   uu___4))
                                                     | uu___4 ->
                                                         Obj.repr
                                                           (FStar_Tactics_Effect.lift_div_tac
                                                              (fun uu___5 ->
                                                                 false))))
                                             else
                                               Obj.magic
                                                 (Obj.repr
                                                    (FStar_Tactics_Effect.lift_div_tac
                                                       (fun uu___5 -> false))))
                                            uu___3)))) uu___1))) uu___)
let rec (solve_gen_unit_elim :
  FStar_Reflection_Types.term ->
    (FStar_Reflection_Types.term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun tl' ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Steel.ST.GenElim1.Base.fsti"
               (Prims.of_int (358)) (Prims.of_int (9)) (Prims.of_int (358))
               (Prims.of_int (40)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Steel.ST.GenElim1.Base.fsti"
               (Prims.of_int (358)) (Prims.of_int (6)) (Prims.of_int (372))
               (Prims.of_int (47)))))
      (Obj.magic
         (FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Steel.ST.GenElim1.Base.fsti"
                     (Prims.of_int (358)) (Prims.of_int (13))
                     (Prims.of_int (358)) (Prims.of_int (40)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Steel.ST.GenElim1.Base.fsti"
                     (Prims.of_int (358)) (Prims.of_int (9))
                     (Prims.of_int (358)) (Prims.of_int (40)))))
            (Obj.magic
               (term_has_head tl'
                  (FStar_Reflection_V2_Builtins.pack_ln
                     (FStar_Reflection_V2_Data.Tv_FVar
                        (FStar_Reflection_V2_Builtins.pack_fv
                           ["Steel"; "ST"; "Util"; "pure"])))))
            (fun uu___ ->
               FStar_Tactics_Effect.lift_div_tac
                 (fun uu___1 -> Prims.op_Negation uu___))))
      (fun uu___ ->
         (fun uu___ ->
            if uu___
            then
              Obj.magic
                (Obj.repr
                   (FStar_Tactics_Effect.lift_div_tac
                      (fun uu___1 ->
                         FStar_Reflection_V1_Derived.mk_app
                           (FStar_Reflection_V2_Builtins.pack_ln
                              (FStar_Reflection_V2_Data.Tv_FVar
                                 (FStar_Reflection_V2_Builtins.pack_fv
                                    ["Steel";
                                    "ST";
                                    "GenElim1";
                                    "Base";
                                    "GUEId"])))
                           [(tl', FStar_Reflection_V1_Data.Q_Explicit)])))
            else
              Obj.magic
                (Obj.repr
                   (FStar_Tactics_Effect.tac_bind
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range
                               "Steel.ST.GenElim1.Base.fsti"
                               (Prims.of_int (361)) (Prims.of_int (23))
                               (Prims.of_int (361)) (Prims.of_int (40)))))
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range
                               "Steel.ST.GenElim1.Base.fsti"
                               (Prims.of_int (360)) (Prims.of_int (10))
                               (Prims.of_int (372)) (Prims.of_int (47)))))
                      (Obj.magic
                         (FStar_Tactics_V1_SyntaxHelpers.collect_app tl'))
                      (fun uu___2 ->
                         (fun uu___2 ->
                            match uu___2 with
                            | (hd, tl) ->
                                if is_fvar hd "Steel.ST.Util.pure"
                                then
                                  Obj.magic
                                    (Obj.repr
                                       (FStar_Tactics_Effect.lift_div_tac
                                          (fun uu___3 ->
                                             FStar_Reflection_V1_Derived.mk_app
                                               (FStar_Reflection_V2_Builtins.pack_ln
                                                  (FStar_Reflection_V2_Data.Tv_FVar
                                                     (FStar_Reflection_V2_Builtins.pack_fv
                                                        ["Steel";
                                                        "ST";
                                                        "GenElim1";
                                                        "Base";
                                                        "GUEPure"]))) tl)))
                                else
                                  Obj.magic
                                    (Obj.repr
                                       (FStar_Tactics_Effect.tac_bind
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Steel.ST.GenElim1.Base.fsti"
                                                   (Prims.of_int (364))
                                                   (Prims.of_int (16))
                                                   (Prims.of_int (364))
                                                   (Prims.of_int (35)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "Steel.ST.GenElim1.Base.fsti"
                                                   (Prims.of_int (364))
                                                   (Prims.of_int (13))
                                                   (Prims.of_int (372))
                                                   (Prims.of_int (47)))))
                                          (Obj.magic (is_star_or_vstar hd))
                                          (fun uu___4 ->
                                             (fun uu___4 ->
                                                if uu___4
                                                then
                                                  Obj.magic
                                                    (Obj.repr
                                                       (match tl with
                                                        | (t1,
                                                           FStar_Reflection_V1_Data.Q_Explicit)::
                                                            (t2,
                                                             FStar_Reflection_V1_Data.Q_Explicit)::[]
                                                            ->
                                                            Obj.repr
                                                              (FStar_Tactics_Effect.tac_bind
                                                                 (FStar_Sealed.seal
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (367))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (367))
                                                                    (Prims.of_int (42)))))
                                                                 (FStar_Sealed.seal
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (367))
                                                                    (Prims.of_int (45))
                                                                    (Prims.of_int (369))
                                                                    (Prims.of_int (68)))))
                                                                 (Obj.magic
                                                                    (
                                                                    solve_gen_unit_elim
                                                                    t1))
                                                                 (fun uu___5
                                                                    ->
                                                                    (fun t1'
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (368))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (368))
                                                                    (Prims.of_int (42)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (369))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (369))
                                                                    (Prims.of_int (68)))))
                                                                    (Obj.magic
                                                                    (solve_gen_unit_elim
                                                                    t2))
                                                                    (fun t2'
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Reflection_V1_Derived.mk_app
                                                                    (FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_FVar
                                                                    (FStar_Reflection_V2_Builtins.pack_fv
                                                                    ["Steel";
                                                                    "ST";
                                                                    "GenElim1";
                                                                    "Base";
                                                                    "GUEStar"])))
                                                                    [
                                                                    (t1',
                                                                    FStar_Reflection_V1_Data.Q_Explicit);
                                                                    (t2',
                                                                    FStar_Reflection_V1_Data.Q_Explicit)]))))
                                                                    uu___5))
                                                        | uu___5 ->
                                                            Obj.repr
                                                              (FStar_Tactics_V1_Derived.fail
                                                                 "ill-formed star")))
                                                else
                                                  Obj.magic
                                                    (Obj.repr
                                                       (FStar_Tactics_Effect.lift_div_tac
                                                          (fun uu___6 ->
                                                             FStar_Reflection_V1_Derived.mk_app
                                                               (FStar_Reflection_V2_Builtins.pack_ln
                                                                  (FStar_Reflection_V2_Data.Tv_FVar
                                                                    (FStar_Reflection_V2_Builtins.pack_fv
                                                                    ["Steel";
                                                                    "ST";
                                                                    "GenElim1";
                                                                    "Base";
                                                                    "GUEId"])))
                                                               [(tl',
                                                                  FStar_Reflection_V1_Data.Q_Explicit)]))))
                                               uu___4)))) uu___2)))) uu___)
let (abstr_has_exists :
  FStar_Reflection_Types.term ->
    (Prims.bool, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun t ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Steel.ST.GenElim1.Base.fsti"
               (Prims.of_int (377)) (Prims.of_int (8)) (Prims.of_int (377))
               (Prims.of_int (19)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Steel.ST.GenElim1.Base.fsti"
               (Prims.of_int (377)) (Prims.of_int (2)) (Prims.of_int (379))
               (Prims.of_int (14)))))
      (Obj.magic (FStar_Tactics_V1_Builtins.inspect t))
      (fun uu___ ->
         (fun uu___ ->
            match uu___ with
            | FStar_Reflection_V1_Data.Tv_Abs (uu___1, body) ->
                Obj.magic
                  (Obj.repr
                     (term_has_head body
                        (FStar_Reflection_V2_Builtins.pack_ln
                           (FStar_Reflection_V2_Data.Tv_FVar
                              (FStar_Reflection_V2_Builtins.pack_fv
                                 ["Steel"; "ST"; "Util"; "exists_"])))))
            | uu___1 ->
                Obj.magic
                  (Obj.repr
                     (FStar_Tactics_Effect.lift_div_tac (fun uu___2 -> false))))
           uu___)
let rec (get_universe :
  FStar_Reflection_Types.universe ->
    (Prims.nat, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___ ->
    (fun u ->
       match FStar_Reflection_V1_Builtins.inspect_universe u with
       | FStar_Reflection_V1_Data.Uv_Zero ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.lift_div_tac
                   (fun uu___ -> Prims.int_zero)))
       | FStar_Reflection_V1_Data.Uv_Succ u1 ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Steel.ST.GenElim1.Base.fsti"
                            (Prims.of_int (386)) (Prims.of_int (23))
                            (Prims.of_int (386)) (Prims.of_int (37)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Steel.ST.GenElim1.Base.fsti"
                            (Prims.of_int (386)) (Prims.of_int (19))
                            (Prims.of_int (386)) (Prims.of_int (37)))))
                   (Obj.magic (get_universe u1))
                   (fun uu___ ->
                      FStar_Tactics_Effect.lift_div_tac
                        (fun uu___1 -> Prims.int_one + uu___))))
       | uu___ ->
           Obj.magic
             (Obj.repr
                (FStar_Tactics_V1_Derived.fail
                   "get_universe: not an universe instantiation"))) uu___
let rec (solve_gen_elim :
  FStar_Reflection_Types.term ->
    (FStar_Reflection_Types.term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun tl' ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Steel.ST.GenElim1.Base.fsti"
               (Prims.of_int (393)) (Prims.of_int (9)) (Prims.of_int (393))
               (Prims.of_int (43)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Steel.ST.GenElim1.Base.fsti"
               (Prims.of_int (393)) (Prims.of_int (6)) (Prims.of_int (458))
               (Prims.of_int (68)))))
      (Obj.magic
         (FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Steel.ST.GenElim1.Base.fsti"
                     (Prims.of_int (393)) (Prims.of_int (13))
                     (Prims.of_int (393)) (Prims.of_int (43)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Steel.ST.GenElim1.Base.fsti"
                     (Prims.of_int (393)) (Prims.of_int (9))
                     (Prims.of_int (393)) (Prims.of_int (43)))))
            (Obj.magic
               (term_has_head tl'
                  (FStar_Reflection_V2_Builtins.pack_ln
                     (FStar_Reflection_V2_Data.Tv_FVar
                        (FStar_Reflection_V2_Builtins.pack_fv
                           ["Steel"; "ST"; "Util"; "exists_"])))))
            (fun uu___ ->
               FStar_Tactics_Effect.lift_div_tac
                 (fun uu___1 -> Prims.op_Negation uu___))))
      (fun uu___ ->
         (fun uu___ ->
            if uu___
            then
              Obj.magic
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Steel.ST.GenElim1.Base.fsti"
                            (Prims.of_int (395)) (Prims.of_int (17))
                            (Prims.of_int (395)) (Prims.of_int (40)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Steel.ST.GenElim1.Base.fsti"
                            (Prims.of_int (396)) (Prims.of_int (8))
                            (Prims.of_int (396)) (Prims.of_int (45)))))
                   (Obj.magic (solve_gen_unit_elim tl'))
                   (fun t' ->
                      FStar_Tactics_Effect.lift_div_tac
                        (fun uu___1 ->
                           FStar_Reflection_V1_Derived.mk_app
                             (FStar_Reflection_V2_Builtins.pack_ln
                                (FStar_Reflection_V2_Data.Tv_FVar
                                   (FStar_Reflection_V2_Builtins.pack_fv
                                      ["Steel";
                                      "ST";
                                      "GenElim1";
                                      "Base";
                                      "GEUnit"])))
                             [(t', FStar_Reflection_V1_Data.Q_Explicit)])))
            else
              Obj.magic
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Steel.ST.GenElim1.Base.fsti"
                            (Prims.of_int (398)) (Prims.of_int (26))
                            (Prims.of_int (398)) (Prims.of_int (43)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "Steel.ST.GenElim1.Base.fsti"
                            (Prims.of_int (397)) (Prims.of_int (14))
                            (Prims.of_int (458)) (Prims.of_int (68)))))
                   (Obj.magic
                      (FStar_Tactics_V1_SyntaxHelpers.collect_app tl'))
                   (fun uu___2 ->
                      (fun uu___2 ->
                         match uu___2 with
                         | (hd, lbody) ->
                             if is_fvar hd "Steel.ST.Util.exists_"
                             then
                               Obj.magic
                                 (FStar_Tactics_Effect.tac_bind
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "Steel.ST.GenElim1.Base.fsti"
                                             (Prims.of_int (401))
                                             (Prims.of_int (25))
                                             (Prims.of_int (403))
                                             (Prims.of_int (63)))))
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "Steel.ST.GenElim1.Base.fsti"
                                             (Prims.of_int (404))
                                             (Prims.of_int (12))
                                             (Prims.of_int (437))
                                             (Prims.of_int (13)))))
                                    (match FStar_Reflection_V1_Derived.inspect_ln_unascribe
                                             hd
                                     with
                                     | FStar_Reflection_V1_Data.Tv_UInst
                                         (uu___3, u::uu___4) ->
                                         Obj.magic
                                           (Obj.repr (get_universe u))
                                     | uu___3 ->
                                         Obj.magic
                                           (Obj.repr
                                              (FStar_Tactics_V1_Derived.fail
                                                 "ill-formed exists_: no universe found")))
                                    (fun uu___3 ->
                                       (fun universe ->
                                          Obj.magic
                                            (FStar_Tactics_Effect.tac_bind
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "Steel.ST.GenElim1.Base.fsti"
                                                        (Prims.of_int (406))
                                                        (Prims.of_int (12))
                                                        (Prims.of_int (409))
                                                        (Prims.of_int (46)))))
                                               (FStar_Sealed.seal
                                                  (Obj.magic
                                                     (FStar_Range.mk_range
                                                        "Steel.ST.GenElim1.Base.fsti"
                                                        (Prims.of_int (404))
                                                        (Prims.of_int (12))
                                                        (Prims.of_int (437))
                                                        (Prims.of_int (13)))))
                                               (match lbody with
                                                | (ty,
                                                   FStar_Reflection_V1_Data.Q_Implicit)::
                                                    (body,
                                                     FStar_Reflection_V1_Data.Q_Explicit)::[]
                                                    ->
                                                    FStar_Tactics_Effect.lift_div_tac
                                                      (fun uu___3 ->
                                                         ([(ty,
                                                             FStar_Reflection_V1_Data.Q_Implicit)],
                                                           body))
                                                | (body,
                                                   FStar_Reflection_V1_Data.Q_Explicit)::[]
                                                    ->
                                                    FStar_Tactics_Effect.lift_div_tac
                                                      (fun uu___3 ->
                                                         ([], body))
                                                | uu___3 ->
                                                    FStar_Tactics_V1_Derived.fail
                                                      "ill-formed exists_")
                                               (fun uu___3 ->
                                                  (fun uu___3 ->
                                                     match uu___3 with
                                                     | (ty, body) ->
                                                         Obj.magic
                                                           (FStar_Tactics_Effect.tac_bind
                                                              (FStar_Sealed.seal
                                                                 (Obj.magic
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (411))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (411))
                                                                    (Prims.of_int (36)))))
                                                              (FStar_Sealed.seal
                                                                 (Obj.magic
                                                                    (
                                                                    FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (411))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (436))
                                                                    (Prims.of_int (21)))))
                                                              (Obj.magic
                                                                 (FStar_Tactics_V1_Builtins.inspect
                                                                    body))
                                                              (fun uu___4 ->
                                                                 (fun uu___4
                                                                    ->
                                                                    match uu___4
                                                                    with
                                                                    | 
                                                                    FStar_Reflection_V1_Data.Tv_Abs
                                                                    (b,
                                                                    abody) ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (413))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (413))
                                                                    (Prims.of_int (53)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (413))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (429))
                                                                    (Prims.of_int (75)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (413))
                                                                    (Prims.of_int (21))
                                                                    (Prims.of_int (413))
                                                                    (Prims.of_int (53)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (413))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (413))
                                                                    (Prims.of_int (53)))))
                                                                    (Obj.magic
                                                                    (term_has_head
                                                                    abody
                                                                    (FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_FVar
                                                                    (FStar_Reflection_V2_Builtins.pack_fv
                                                                    ["Steel";
                                                                    "ST";
                                                                    "Util";
                                                                    "exists_"])))))
                                                                    (fun
                                                                    uu___5 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    Prims.op_Negation
                                                                    uu___5))))
                                                                    (fun
                                                                    uu___5 ->
                                                                    (fun
                                                                    uu___5 ->
                                                                    if uu___5
                                                                    then
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (415))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (415))
                                                                    (Prims.of_int (53)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (416))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (421))
                                                                    (Prims.of_int (75)))))
                                                                    (Obj.magic
                                                                    (solve_gen_unit_elim
                                                                    abody))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    body' ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (421))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (421))
                                                                    (Prims.of_int (75)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (416))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (421))
                                                                    (Prims.of_int (75)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (421))
                                                                    (Prims.of_int (40))
                                                                    (Prims.of_int (421))
                                                                    (Prims.of_int (74)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (421))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (421))
                                                                    (Prims.of_int (75)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (421))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (421))
                                                                    (Prims.of_int (73)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (421))
                                                                    (Prims.of_int (40))
                                                                    (Prims.of_int (421))
                                                                    (Prims.of_int (74)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (421))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (421))
                                                                    (Prims.of_int (59)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (421))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (421))
                                                                    (Prims.of_int (73)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_V1_Derived.mk_abs
                                                                    [b] body'))
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    (uu___6,
                                                                    FStar_Reflection_V1_Data.Q_Explicit)))))
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    [uu___6]))))
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    FStar_List_Tot_Base.append
                                                                    ty uu___6))))
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    FStar_Reflection_V1_Derived.mk_app
                                                                    (match universe
                                                                    with
                                                                    | 
                                                                    uu___8
                                                                    when
                                                                    uu___8 =
                                                                    Prims.int_zero
                                                                    ->
                                                                    FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_FVar
                                                                    (FStar_Reflection_V2_Builtins.pack_fv
                                                                    ["Steel";
                                                                    "ST";
                                                                    "GenElim1";
                                                                    "Base";
                                                                    "GEExistsUnit0"]))
                                                                    | 
                                                                    uu___8 ->
                                                                    FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_FVar
                                                                    (FStar_Reflection_V2_Builtins.pack_fv
                                                                    ["Steel";
                                                                    "ST";
                                                                    "GenElim1";
                                                                    "Base";
                                                                    "GEExistsUnit1"])))
                                                                    uu___6))))
                                                                    uu___6))
                                                                    else
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (423))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (423))
                                                                    (Prims.of_int (48)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (424))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (429))
                                                                    (Prims.of_int (75)))))
                                                                    (Obj.magic
                                                                    (solve_gen_elim
                                                                    abody))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    body' ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (429))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (429))
                                                                    (Prims.of_int (75)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (424))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (429))
                                                                    (Prims.of_int (75)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (429))
                                                                    (Prims.of_int (40))
                                                                    (Prims.of_int (429))
                                                                    (Prims.of_int (74)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (429))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (429))
                                                                    (Prims.of_int (75)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (429))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (429))
                                                                    (Prims.of_int (73)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (429))
                                                                    (Prims.of_int (40))
                                                                    (Prims.of_int (429))
                                                                    (Prims.of_int (74)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (429))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (429))
                                                                    (Prims.of_int (59)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (429))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (429))
                                                                    (Prims.of_int (73)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_V1_Derived.mk_abs
                                                                    [b] body'))
                                                                    (fun
                                                                    uu___7 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    (uu___7,
                                                                    FStar_Reflection_V1_Data.Q_Explicit)))))
                                                                    (fun
                                                                    uu___7 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    [uu___7]))))
                                                                    (fun
                                                                    uu___7 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    FStar_List_Tot_Base.append
                                                                    ty uu___7))))
                                                                    (fun
                                                                    uu___7 ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    FStar_Reflection_V1_Derived.mk_app
                                                                    (match universe
                                                                    with
                                                                    | 
                                                                    uu___9
                                                                    when
                                                                    uu___9 =
                                                                    Prims.int_zero
                                                                    ->
                                                                    FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_FVar
                                                                    (FStar_Reflection_V2_Builtins.pack_fv
                                                                    ["Steel";
                                                                    "ST";
                                                                    "GenElim1";
                                                                    "Base";
                                                                    "GEExists0"]))
                                                                    | 
                                                                    uu___9 ->
                                                                    FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_FVar
                                                                    (FStar_Reflection_V2_Builtins.pack_fv
                                                                    ["Steel";
                                                                    "ST";
                                                                    "GenElim1";
                                                                    "Base";
                                                                    "GEExists1"])))
                                                                    uu___7))))
                                                                    uu___7)))
                                                                    uu___5)))
                                                                    | 
                                                                    uu___5 ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Reflection_V1_Derived.mk_app
                                                                    (match universe
                                                                    with
                                                                    | 
                                                                    uu___7
                                                                    when
                                                                    uu___7 =
                                                                    Prims.int_zero
                                                                    ->
                                                                    FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_FVar
                                                                    (FStar_Reflection_V2_Builtins.pack_fv
                                                                    ["Steel";
                                                                    "ST";
                                                                    "GenElim1";
                                                                    "Base";
                                                                    "GEExistsNoAbs0"]))
                                                                    | 
                                                                    uu___7 ->
                                                                    FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_FVar
                                                                    (FStar_Reflection_V2_Builtins.pack_fv
                                                                    ["Steel";
                                                                    "ST";
                                                                    "GenElim1";
                                                                    "Base";
                                                                    "GEExistsNoAbs1"])))
                                                                    lbody))))
                                                                   uu___4)))
                                                    uu___3))) uu___3))
                             else
                               Obj.magic
                                 (FStar_Tactics_Effect.tac_bind
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "Steel.ST.GenElim1.Base.fsti"
                                             (Prims.of_int (438))
                                             (Prims.of_int (16))
                                             (Prims.of_int (438))
                                             (Prims.of_int (35)))))
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "Steel.ST.GenElim1.Base.fsti"
                                             (Prims.of_int (438))
                                             (Prims.of_int (13))
                                             (Prims.of_int (458))
                                             (Prims.of_int (68)))))
                                    (Obj.magic (is_star_or_vstar hd))
                                    (fun uu___4 ->
                                       (fun uu___4 ->
                                          if uu___4
                                          then
                                            Obj.magic
                                              (Obj.repr
                                                 (match lbody with
                                                  | (tl,
                                                     FStar_Reflection_V1_Data.Q_Explicit)::
                                                      (tr,
                                                       FStar_Reflection_V1_Data.Q_Explicit)::[]
                                                      ->
                                                      Obj.repr
                                                        (FStar_Tactics_Effect.tac_bind
                                                           (FStar_Sealed.seal
                                                              (Obj.magic
                                                                 (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (442))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (442))
                                                                    (Prims.of_int (42)))))
                                                           (FStar_Sealed.seal
                                                              (Obj.magic
                                                                 (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (442))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (455))
                                                                    (Prims.of_int (72)))))
                                                           (Obj.magic
                                                              (term_has_head
                                                                 tl
                                                                 (FStar_Reflection_V2_Builtins.pack_ln
                                                                    (
                                                                    FStar_Reflection_V2_Data.Tv_FVar
                                                                    (FStar_Reflection_V2_Builtins.pack_fv
                                                                    ["Steel";
                                                                    "ST";
                                                                    "Util";
                                                                    "exists_"])))))
                                                           (fun uu___5 ->
                                                              (fun uu___5 ->
                                                                 if uu___5
                                                                 then
                                                                   Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (444))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (444))
                                                                    (Prims.of_int (41)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (445))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (451))
                                                                    (Prims.of_int (74)))))
                                                                    (Obj.magic
                                                                    (solve_gen_elim
                                                                    tl))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun tl'1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (445))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (445))
                                                                    (Prims.of_int (44)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (445))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (451))
                                                                    (Prims.of_int (74)))))
                                                                    (Obj.magic
                                                                    (term_has_head
                                                                    tr
                                                                    (FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_FVar
                                                                    (FStar_Reflection_V2_Builtins.pack_fv
                                                                    ["Steel";
                                                                    "ST";
                                                                    "Util";
                                                                    "exists_"])))))
                                                                    (fun
                                                                    uu___6 ->
                                                                    (fun
                                                                    uu___6 ->
                                                                    if uu___6
                                                                    then
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (447))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (447))
                                                                    (Prims.of_int (43)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (448))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (448))
                                                                    (Prims.of_int (73)))))
                                                                    (Obj.magic
                                                                    (solve_gen_elim
                                                                    tr))
                                                                    (fun tr'
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    FStar_Reflection_V1_Derived.mk_app
                                                                    (FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_FVar
                                                                    (FStar_Reflection_V2_Builtins.pack_fv
                                                                    ["Steel";
                                                                    "ST";
                                                                    "GenElim1";
                                                                    "Base";
                                                                    "GEStar"])))
                                                                    [
                                                                    (tl'1,
                                                                    FStar_Reflection_V1_Data.Q_Explicit);
                                                                    (tr',
                                                                    FStar_Reflection_V1_Data.Q_Explicit)])))
                                                                    else
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (450))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (450))
                                                                    (Prims.of_int (48)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (451))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (451))
                                                                    (Prims.of_int (74)))))
                                                                    (Obj.magic
                                                                    (solve_gen_unit_elim
                                                                    tr))
                                                                    (fun tr'
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    FStar_Reflection_V1_Derived.mk_app
                                                                    (FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_FVar
                                                                    (FStar_Reflection_V2_Builtins.pack_fv
                                                                    ["Steel";
                                                                    "ST";
                                                                    "GenElim1";
                                                                    "Base";
                                                                    "GEStarL"])))
                                                                    [
                                                                    (tl'1,
                                                                    FStar_Reflection_V1_Data.Q_Explicit);
                                                                    (tr',
                                                                    FStar_Reflection_V1_Data.Q_Explicit)]))))
                                                                    uu___6)))
                                                                    uu___6))
                                                                 else
                                                                   Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (453))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (453))
                                                                    (Prims.of_int (46)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (453))
                                                                    (Prims.of_int (49))
                                                                    (Prims.of_int (455))
                                                                    (Prims.of_int (72)))))
                                                                    (Obj.magic
                                                                    (solve_gen_unit_elim
                                                                    tl))
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun tl'1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (454))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (454))
                                                                    (Prims.of_int (41)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (455))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (455))
                                                                    (Prims.of_int (72)))))
                                                                    (Obj.magic
                                                                    (solve_gen_elim
                                                                    tr))
                                                                    (fun tr'
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    FStar_Reflection_V1_Derived.mk_app
                                                                    (FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_FVar
                                                                    (FStar_Reflection_V2_Builtins.pack_fv
                                                                    ["Steel";
                                                                    "ST";
                                                                    "GenElim1";
                                                                    "Base";
                                                                    "GEStarR"])))
                                                                    [
                                                                    (tl'1,
                                                                    FStar_Reflection_V1_Data.Q_Explicit);
                                                                    (tr',
                                                                    FStar_Reflection_V1_Data.Q_Explicit)]))))
                                                                    uu___7)))
                                                                uu___5))
                                                  | uu___5 ->
                                                      Obj.repr
                                                        (FStar_Tactics_V1_Derived.fail
                                                           "ill-formed star")))
                                          else
                                            Obj.magic
                                              (Obj.repr
                                                 (FStar_Tactics_Effect.lift_div_tac
                                                    (fun uu___6 ->
                                                       FStar_Reflection_V1_Derived.mk_app
                                                         (FStar_Reflection_V2_Builtins.pack_ln
                                                            (FStar_Reflection_V2_Data.Tv_FVar
                                                               (FStar_Reflection_V2_Builtins.pack_fv
                                                                  ["Steel";
                                                                  "ST";
                                                                  "GenElim1";
                                                                  "Base";
                                                                  "GEUnit"])))
                                                         [((FStar_Reflection_V1_Derived.mk_app
                                                              (FStar_Reflection_V2_Builtins.pack_ln
                                                                 (FStar_Reflection_V2_Data.Tv_FVar
                                                                    (
                                                                    FStar_Reflection_V2_Builtins.pack_fv
                                                                    ["Steel";
                                                                    "ST";
                                                                    "GenElim1";
                                                                    "Base";
                                                                    "GUEId"])))
                                                              lbody),
                                                            FStar_Reflection_V1_Data.Q_Explicit)]))))
                                         uu___4))) uu___2))) uu___)
let rec (solve_gen_elim_nondep' :
  Prims.nat ->
    (FStar_Reflection_Types.term * FStar_Reflection_Types.binder) Prims.list
      ->
      FStar_Reflection_Types.term ->
        ((FStar_Reflection_Types.term * FStar_Reflection_Types.term *
           FStar_Reflection_Types.term * FStar_Reflection_Types.term *
           FStar_Reflection_Types.term) FStar_Pervasives_Native.option,
          unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___2 ->
    fun uu___1 ->
      fun uu___ ->
        (fun fuel ->
           fun rev_types_and_binders ->
             fun t ->
               if fuel = Prims.int_zero
               then
                 Obj.magic
                   (Obj.repr
                      (FStar_Tactics_Effect.lift_div_tac
                         (fun uu___ -> FStar_Pervasives_Native.None)))
               else
                 Obj.magic
                   (Obj.repr
                      (FStar_Tactics_Effect.tac_bind
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "Steel.ST.GenElim1.Base.fsti"
                                  (Prims.of_int (547)) (Prims.of_int (19))
                                  (Prims.of_int (547)) (Prims.of_int (34)))))
                         (FStar_Sealed.seal
                            (Obj.magic
                               (FStar_Range.mk_range
                                  "Steel.ST.GenElim1.Base.fsti"
                                  (Prims.of_int (546)) (Prims.of_int (6))
                                  (Prims.of_int (592)) (Prims.of_int (13)))))
                         (Obj.magic
                            (FStar_Tactics_V1_SyntaxHelpers.collect_app t))
                         (fun uu___1 ->
                            (fun uu___1 ->
                               match uu___1 with
                               | (hd, tl) ->
                                   if
                                     is_fvar hd "Steel.ST.GenElim1.Base.TRet"
                                   then
                                     (match tl with
                                      | (v,
                                         FStar_Reflection_V1_Data.Q_Explicit)::
                                          (p,
                                           FStar_Reflection_V1_Data.Q_Explicit)::[]
                                          ->
                                          Obj.magic
                                            (Obj.repr
                                               (FStar_Tactics_Effect.tac_bind
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "Steel.ST.GenElim1.Base.fsti"
                                                           (Prims.of_int (551))
                                                           (Prims.of_int (96))
                                                           (Prims.of_int (554))
                                                           (Prims.of_int (88)))))
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "Steel.ST.GenElim1.Base.fsti"
                                                           (Prims.of_int (555))
                                                           (Prims.of_int (8))
                                                           (Prims.of_int (582))
                                                           (Prims.of_int (9)))))
                                                  (FStar_Tactics_Effect.lift_div_tac
                                                     (fun uu___2 ->
                                                        fun accu ->
                                                          fun tb ->
                                                            fun uu___3 ->
                                                              FStar_Tactics_Effect.tac_bind
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (552))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (552))
                                                                    (Prims.of_int (24)))))
                                                                (FStar_Sealed.seal
                                                                   (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (551))
                                                                    (Prims.of_int (96))
                                                                    (Prims.of_int (554))
                                                                    (Prims.of_int (88)))))
                                                                (FStar_Tactics_Effect.lift_div_tac
                                                                   (fun
                                                                    uu___4 ->
                                                                    tb))
                                                                (fun uu___4
                                                                   ->
                                                                   (fun
                                                                    uu___4 ->
                                                                    match uu___4
                                                                    with
                                                                    | 
                                                                    (ty,
                                                                    uu___5)
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (553))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (553))
                                                                    (Prims.of_int (24)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (554))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (554))
                                                                    (Prims.of_int (88)))))
                                                                    (Obj.magic
                                                                    (accu ()))
                                                                    (fun tl1
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Reflection_V1_Derived.mk_app
                                                                    (FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_FVar
                                                                    (FStar_Reflection_V2_Builtins.pack_fv
                                                                    ["Prims";
                                                                    "Cons"])))
                                                                    [
                                                                    ((FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_Type
                                                                    (FStar_Reflection_V2_Builtins.pack_universe
                                                                    (FStar_Reflection_V2_Data.Uv_Succ
                                                                    (FStar_Reflection_V2_Builtins.pack_universe
                                                                    FStar_Reflection_V2_Data.Uv_Zero))))),
                                                                    FStar_Reflection_V1_Data.Q_Implicit);
                                                                    (ty,
                                                                    FStar_Reflection_V1_Data.Q_Explicit);
                                                                    (tl1,
                                                                    FStar_Reflection_V1_Data.Q_Explicit)]))))
                                                                    uu___4)))
                                                  (fun uu___2 ->
                                                     (fun cons_type ->
                                                        Obj.magic
                                                          (FStar_Tactics_Effect.tac_bind
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (556))
                                                                    (Prims.of_int (39))
                                                                    (Prims.of_int (556))
                                                                    (Prims.of_int (84)))))
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (556))
                                                                    (Prims.of_int (87))
                                                                    (Prims.of_int (582))
                                                                    (Prims.of_int (9)))))
                                                             (FStar_Tactics_Effect.lift_div_tac
                                                                (fun uu___3
                                                                   ->
                                                                   fun uu___2
                                                                    ->
                                                                    (fun
                                                                    uu___2 ->
                                                                    fun
                                                                    uu___3 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___4 ->
                                                                    FStar_Reflection_V1_Derived.mk_app
                                                                    (FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_FVar
                                                                    (FStar_Reflection_V2_Builtins.pack_fv
                                                                    ["Prims";
                                                                    "Nil"])))
                                                                    [
                                                                    ((FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_Type
                                                                    (FStar_Reflection_V2_Builtins.pack_universe
                                                                    (FStar_Reflection_V2_Data.Uv_Succ
                                                                    (FStar_Reflection_V2_Builtins.pack_universe
                                                                    FStar_Reflection_V2_Data.Uv_Zero))))),
                                                                    FStar_Reflection_V1_Data.Q_Implicit)])))
                                                                    uu___3
                                                                    uu___2))
                                                             (fun uu___2 ->
                                                                (fun nil_type
                                                                   ->
                                                                   Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (557))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (557))
                                                                    (Prims.of_int (84)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (557))
                                                                    (Prims.of_int (87))
                                                                    (Prims.of_int (582))
                                                                    (Prims.of_int (9)))))
                                                                    (Obj.magic
                                                                    (FStar_List_Tot_Base.fold_left
                                                                    cons_type
                                                                    nil_type
                                                                    rev_types_and_binders
                                                                    ()))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    type_list
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (560))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (564))
                                                                    (Prims.of_int (23)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (566))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (582))
                                                                    (Prims.of_int (9)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_V1_Derived.try_with
                                                                    (fun
                                                                    uu___2 ->
                                                                    match ()
                                                                    with
                                                                    | 
                                                                    () ->
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (561))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (561))
                                                                    (Prims.of_int (30)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (561))
                                                                    (Prims.of_int (33))
                                                                    (Prims.of_int (563))
                                                                    (Prims.of_int (47)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_V1_Derived.cur_env
                                                                    ()))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun env
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (562))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (562))
                                                                    (Prims.of_int (35)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (563))
                                                                    (Prims.of_int (10))
                                                                    (Prims.of_int (563))
                                                                    (Prims.of_int (47)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_V1_Builtins.tc
                                                                    env
                                                                    type_list))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun ty
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_V1_Builtins.term_eq_old
                                                                    ty
                                                                    (FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_App
                                                                    ((FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_FVar
                                                                    (FStar_Reflection_V2_Builtins.pack_fv
                                                                    ["Prims";
                                                                    "list"]))),
                                                                    ((FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_Type
                                                                    (FStar_Reflection_V2_Builtins.pack_universe
                                                                    (FStar_Reflection_V2_Data.Uv_Succ
                                                                    (FStar_Reflection_V2_Builtins.pack_universe
                                                                    FStar_Reflection_V2_Data.Uv_Zero))))),
                                                                    FStar_Reflection_V2_Data.Q_Explicit))))))
                                                                    uu___3)))
                                                                    uu___3))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    uu___2 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    false)))
                                                                    uu___2)))
                                                                    (fun
                                                                    uu___2 ->
                                                                    (fun
                                                                    type_list_typechecks
                                                                    ->
                                                                    if
                                                                    Prims.op_Negation
                                                                    type_list_typechecks
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___2 ->
                                                                    FStar_Pervasives_Native.None)))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (569))
                                                                    (Prims.of_int (39))
                                                                    (Prims.of_int (569))
                                                                    (Prims.of_int (81)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (569))
                                                                    (Prims.of_int (84))
                                                                    (Prims.of_int (582))
                                                                    (Prims.of_int (9)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_V1_Derived.fresh_binder
                                                                    (FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_App
                                                                    ((FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_UInst
                                                                    ((FStar_Reflection_V2_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Universe";
                                                                    "raise_t"]),
                                                                    [
                                                                    FStar_Reflection_V2_Builtins.pack_universe
                                                                    FStar_Reflection_V2_Data.Uv_Unk;
                                                                    FStar_Reflection_V2_Builtins.pack_universe
                                                                    (FStar_Reflection_V2_Data.Uv_Succ
                                                                    (FStar_Reflection_V2_Builtins.pack_universe
                                                                    (FStar_Reflection_V2_Data.Uv_Succ
                                                                    (FStar_Reflection_V2_Builtins.pack_universe
                                                                    FStar_Reflection_V2_Data.Uv_Zero))))]))),
                                                                    ((FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_FVar
                                                                    (FStar_Reflection_V2_Builtins.pack_fv
                                                                    ["Prims";
                                                                    "unit"]))),
                                                                    FStar_Reflection_V2_Data.Q_Explicit))))))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    dummy_raised_unit_binder
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (570))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (570))
                                                                    (Prims.of_int (120)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (570))
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (582))
                                                                    (Prims.of_int (9)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_List_Tot_Base.append
                                                                    (FStar_List_Tot_Base.map
                                                                    FStar_Pervasives_Native.snd
                                                                    (FStar_List_Tot_Base.rev
                                                                    rev_types_and_binders))
                                                                    [dummy_raised_unit_binder]))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    binders
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (571))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (571))
                                                                    (Prims.of_int (82)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (571))
                                                                    (Prims.of_int (85))
                                                                    (Prims.of_int (582))
                                                                    (Prims.of_int (9)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Tactics_V1_Derived.norm_term
                                                                    [
                                                                    FStar_Pervasives.delta_attr
                                                                    ["Steel.ST.GenElim1.Base.gen_elim_reduce"];
                                                                    FStar_Pervasives.zeta;
                                                                    FStar_Pervasives.iota]))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun
                                                                    norm_term
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (572))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (572))
                                                                    (Prims.of_int (35)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (572))
                                                                    (Prims.of_int (38))
                                                                    (Prims.of_int (582))
                                                                    (Prims.of_int (9)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_V1_Derived.mk_abs
                                                                    binders v))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun v'
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (573))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (573))
                                                                    (Prims.of_int (151)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (573))
                                                                    (Prims.of_int (154))
                                                                    (Prims.of_int (582))
                                                                    (Prims.of_int (9)))))
                                                                    (Obj.magic
                                                                    (norm_term
                                                                    (FStar_Reflection_V1_Derived.mk_app
                                                                    (FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_UInst
                                                                    ((FStar_Reflection_V2_Builtins.pack_fv
                                                                    ["Steel";
                                                                    "ST";
                                                                    "GenElim1";
                                                                    "Base";
                                                                    "curried_function_type"]),
                                                                    [
                                                                    FStar_Reflection_V2_Builtins.pack_universe
                                                                    (FStar_Reflection_V2_Data.Uv_Succ
                                                                    (FStar_Reflection_V2_Builtins.pack_universe
                                                                    FStar_Reflection_V2_Data.Uv_Zero));
                                                                    FStar_Reflection_V2_Builtins.pack_universe
                                                                    (FStar_Reflection_V2_Data.Uv_Succ
                                                                    (FStar_Reflection_V2_Builtins.pack_universe
                                                                    (FStar_Reflection_V2_Data.Uv_Succ
                                                                    (FStar_Reflection_V2_Builtins.pack_universe
                                                                    FStar_Reflection_V2_Data.Uv_Zero))))])))
                                                                    [
                                                                    (type_list,
                                                                    FStar_Reflection_V1_Data.Q_Explicit);
                                                                    ((FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_Arrow
                                                                    ((FStar_Reflection_V2_Builtins.pack_binder
                                                                    {
                                                                    FStar_Reflection_V2_Data.sort2
                                                                    =
                                                                    (FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_App
                                                                    ((FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_UInst
                                                                    ((FStar_Reflection_V2_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Universe";
                                                                    "raise_t"]),
                                                                    [
                                                                    FStar_Reflection_V2_Builtins.pack_universe
                                                                    FStar_Reflection_V2_Data.Uv_Unk;
                                                                    FStar_Reflection_V2_Builtins.pack_universe
                                                                    (FStar_Reflection_V2_Data.Uv_Succ
                                                                    (FStar_Reflection_V2_Builtins.pack_universe
                                                                    (FStar_Reflection_V2_Data.Uv_Succ
                                                                    (FStar_Reflection_V2_Builtins.pack_universe
                                                                    FStar_Reflection_V2_Data.Uv_Zero))))]))),
                                                                    ((FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_FVar
                                                                    (FStar_Reflection_V2_Builtins.pack_fv
                                                                    ["Prims";
                                                                    "unit"]))),
                                                                    FStar_Reflection_V2_Data.Q_Explicit))));
                                                                    FStar_Reflection_V2_Data.qual
                                                                    =
                                                                    FStar_Reflection_V2_Data.Q_Explicit;
                                                                    FStar_Reflection_V2_Data.attrs
                                                                    = [];
                                                                    FStar_Reflection_V2_Data.ppname2
                                                                    =
                                                                    (FStar_Sealed.seal
                                                                    "_")
                                                                    }),
                                                                    (FStar_Reflection_V2_Builtins.pack_comp
                                                                    (FStar_Reflection_V2_Data.C_Total
                                                                    (FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_FVar
                                                                    (FStar_Reflection_V2_Builtins.pack_fv
                                                                    ["Steel";
                                                                    "Effect";
                                                                    "Common";
                                                                    "vprop"])))))))),
                                                                    FStar_Reflection_V1_Data.Q_Explicit)])))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun tv'
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (574))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (574))
                                                                    (Prims.of_int (35)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (574))
                                                                    (Prims.of_int (38))
                                                                    (Prims.of_int (582))
                                                                    (Prims.of_int (9)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_V1_Derived.mk_abs
                                                                    binders p))
                                                                    (fun
                                                                    uu___3 ->
                                                                    (fun p'
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (575))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (575))
                                                                    (Prims.of_int (150)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (576))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (582))
                                                                    (Prims.of_int (9)))))
                                                                    (Obj.magic
                                                                    (norm_term
                                                                    (FStar_Reflection_V1_Derived.mk_app
                                                                    (FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_UInst
                                                                    ((FStar_Reflection_V2_Builtins.pack_fv
                                                                    ["Steel";
                                                                    "ST";
                                                                    "GenElim1";
                                                                    "Base";
                                                                    "curried_function_type"]),
                                                                    [
                                                                    FStar_Reflection_V2_Builtins.pack_universe
                                                                    (FStar_Reflection_V2_Data.Uv_Succ
                                                                    (FStar_Reflection_V2_Builtins.pack_universe
                                                                    FStar_Reflection_V2_Data.Uv_Zero));
                                                                    FStar_Reflection_V2_Builtins.pack_universe
                                                                    (FStar_Reflection_V2_Data.Uv_Succ
                                                                    (FStar_Reflection_V2_Builtins.pack_universe
                                                                    (FStar_Reflection_V2_Data.Uv_Succ
                                                                    (FStar_Reflection_V2_Builtins.pack_universe
                                                                    FStar_Reflection_V2_Data.Uv_Zero))))])))
                                                                    [
                                                                    (type_list,
                                                                    FStar_Reflection_V1_Data.Q_Explicit);
                                                                    ((FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_Arrow
                                                                    ((FStar_Reflection_V2_Builtins.pack_binder
                                                                    {
                                                                    FStar_Reflection_V2_Data.sort2
                                                                    =
                                                                    (FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_App
                                                                    ((FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_UInst
                                                                    ((FStar_Reflection_V2_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Universe";
                                                                    "raise_t"]),
                                                                    [
                                                                    FStar_Reflection_V2_Builtins.pack_universe
                                                                    FStar_Reflection_V2_Data.Uv_Unk;
                                                                    FStar_Reflection_V2_Builtins.pack_universe
                                                                    (FStar_Reflection_V2_Data.Uv_Succ
                                                                    (FStar_Reflection_V2_Builtins.pack_universe
                                                                    (FStar_Reflection_V2_Data.Uv_Succ
                                                                    (FStar_Reflection_V2_Builtins.pack_universe
                                                                    FStar_Reflection_V2_Data.Uv_Zero))))]))),
                                                                    ((FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_FVar
                                                                    (FStar_Reflection_V2_Builtins.pack_fv
                                                                    ["Prims";
                                                                    "unit"]))),
                                                                    FStar_Reflection_V2_Data.Q_Explicit))));
                                                                    FStar_Reflection_V2_Data.qual
                                                                    =
                                                                    FStar_Reflection_V2_Data.Q_Explicit;
                                                                    FStar_Reflection_V2_Data.attrs
                                                                    = [];
                                                                    FStar_Reflection_V2_Data.ppname2
                                                                    =
                                                                    (FStar_Sealed.seal
                                                                    "_")
                                                                    }),
                                                                    (FStar_Reflection_V2_Builtins.pack_comp
                                                                    (FStar_Reflection_V2_Data.C_Total
                                                                    (FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_FVar
                                                                    (FStar_Reflection_V2_Builtins.pack_fv
                                                                    ["Prims";
                                                                    "prop"])))))))),
                                                                    FStar_Reflection_V1_Data.Q_Explicit)])))
                                                                    (fun tp'
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___3 ->
                                                                    FStar_Pervasives_Native.Some
                                                                    (type_list,
                                                                    tv', v',
                                                                    tp', p')))))
                                                                    uu___3)))
                                                                    uu___3)))
                                                                    uu___3)))
                                                                    uu___3)))
                                                                    uu___3)))
                                                                    uu___3))))
                                                                    uu___2)))
                                                                    uu___2)))
                                                                  uu___2)))
                                                       uu___2)))
                                      | uu___2 ->
                                          Obj.magic
                                            (Obj.repr
                                               (FStar_Tactics_Effect.lift_div_tac
                                                  (fun uu___3 ->
                                                     FStar_Pervasives_Native.None))))
                                   else
                                     if
                                       is_fvar hd
                                         "Steel.ST.GenElim1.Base.TExists"
                                     then
                                       Obj.magic
                                         (Obj.repr
                                            (match tl with
                                             | (ty, uu___3)::(f,
                                                              FStar_Reflection_V1_Data.Q_Explicit)::[]
                                                 ->
                                                 Obj.repr
                                                   (FStar_Tactics_Effect.tac_bind
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "Steel.ST.GenElim1.Base.fsti"
                                                               (Prims.of_int (587))
                                                               (Prims.of_int (18))
                                                               (Prims.of_int (587))
                                                               (Prims.of_int (29)))))
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "Steel.ST.GenElim1.Base.fsti"
                                                               (Prims.of_int (587))
                                                               (Prims.of_int (12))
                                                               (Prims.of_int (589))
                                                               (Prims.of_int (17)))))
                                                      (Obj.magic
                                                         (FStar_Tactics_V1_Builtins.inspect
                                                            f))
                                                      (fun uu___4 ->
                                                         (fun uu___4 ->
                                                            match uu___4 with
                                                            | FStar_Reflection_V1_Data.Tv_Abs
                                                                (bv, body) ->
                                                                Obj.magic
                                                                  (Obj.repr
                                                                    (solve_gen_elim_nondep'
                                                                    (fuel -
                                                                    Prims.int_one)
                                                                    ((ty, bv)
                                                                    ::
                                                                    rev_types_and_binders)
                                                                    body))
                                                            | uu___5 ->
                                                                Obj.magic
                                                                  (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___6 ->
                                                                    FStar_Pervasives_Native.None))))
                                                           uu___4))
                                             | uu___3 ->
                                                 Obj.repr
                                                   (FStar_Tactics_Effect.lift_div_tac
                                                      (fun uu___4 ->
                                                         FStar_Pervasives_Native.None))))
                                     else
                                       Obj.magic
                                         (Obj.repr
                                            (FStar_Tactics_Effect.lift_div_tac
                                               (fun uu___4 ->
                                                  FStar_Pervasives_Native.None))))
                              uu___1)))) uu___2 uu___1 uu___
let (solve_gen_elim_nondep0 :
  Prims.bool ->
    FStar_Reflection_Types.term ->
      ((FStar_Reflection_Types.term * FStar_Reflection_Types.term *
         FStar_Reflection_Types.term * FStar_Reflection_Types.term *
         FStar_Reflection_Types.term) FStar_Pervasives_Native.option,
        unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___1 ->
    fun uu___ ->
      (fun enable_nondep_opt ->
         fun t ->
           if enable_nondep_opt
           then
             Obj.magic
               (Obj.repr
                  (FStar_Tactics_V1_Derived.try_with
                     (fun uu___ ->
                        match () with
                        | () ->
                            FStar_Tactics_Effect.tac_bind
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Steel.ST.GenElim1.Base.fsti"
                                       (Prims.of_int (599))
                                       (Prims.of_int (17))
                                       (Prims.of_int (599))
                                       (Prims.of_int (64)))))
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "Steel.ST.GenElim1.Base.fsti"
                                       (Prims.of_int (599))
                                       (Prims.of_int (67))
                                       (Prims.of_int (601))
                                       (Prims.of_int (37)))))
                              (FStar_Tactics_Effect.lift_div_tac
                                 (fun uu___1 ->
                                    FStar_Reflection_V1_Derived.mk_app
                                      (FStar_Reflection_V2_Builtins.pack_ln
                                         (FStar_Reflection_V2_Data.Tv_FVar
                                            (FStar_Reflection_V2_Builtins.pack_fv
                                               ["Steel";
                                               "ST";
                                               "GenElim1";
                                               "Base";
                                               "compute_gen_elim_tele"])))
                                      [(t,
                                         FStar_Reflection_V1_Data.Q_Explicit)]))
                              (fun uu___1 ->
                                 (fun tele ->
                                    Obj.magic
                                      (FStar_Tactics_Effect.tac_bind
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "Steel.ST.GenElim1.Base.fsti"
                                                  (Prims.of_int (600))
                                                  (Prims.of_int (15))
                                                  (Prims.of_int (600))
                                                  (Prims.of_int (76)))))
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "Steel.ST.GenElim1.Base.fsti"
                                                  (Prims.of_int (601))
                                                  (Prims.of_int (6))
                                                  (Prims.of_int (601))
                                                  (Prims.of_int (37)))))
                                         (Obj.magic
                                            (FStar_Tactics_V1_Derived.norm_term
                                               [FStar_Pervasives.delta_attr
                                                  ["Steel.ST.GenElim1.Base.gen_elim_reduce"];
                                               FStar_Pervasives.zeta;
                                               FStar_Pervasives.iota] tele))
                                         (fun uu___1 ->
                                            (fun t' ->
                                               Obj.magic
                                                 (solve_gen_elim_nondep'
                                                    (Prims.of_int (15)) [] t'))
                                              uu___1))) uu___1))
                     (fun uu___ ->
                        (fun uu___ ->
                           Obj.magic
                             (FStar_Tactics_Effect.lift_div_tac
                                (fun uu___1 -> FStar_Pervasives_Native.None)))
                          uu___)))
           else
             Obj.magic
               (Obj.repr
                  (FStar_Tactics_Effect.lift_div_tac
                     (fun uu___1 -> FStar_Pervasives_Native.None)))) uu___1
        uu___
let (solve_gen_elim_nondep :
  Prims.bool ->
    FStar_Reflection_Types.term ->
      (FStar_Reflection_Types.term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun enable_nondep_opt ->
    fun t ->
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Steel.ST.GenElim1.Base.fsti"
                 (Prims.of_int (606)) (Prims.of_int (8)) (Prims.of_int (606))
                 (Prims.of_int (50)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "Steel.ST.GenElim1.Base.fsti"
                 (Prims.of_int (606)) (Prims.of_int (2)) (Prims.of_int (620))
                 (Prims.of_int (9)))))
        (Obj.magic (solve_gen_elim_nondep0 enable_nondep_opt t))
        (fun uu___ ->
           FStar_Tactics_Effect.lift_div_tac
             (fun uu___1 ->
                match uu___ with
                | FStar_Pervasives_Native.None ->
                    FStar_Reflection_V2_Builtins.pack_ln
                      (FStar_Reflection_V2_Data.Tv_FVar
                         (FStar_Reflection_V2_Builtins.pack_fv
                            ["Steel"; "ST"; "GenElim1"; "Base"; "GEDep"]))
                | FStar_Pervasives_Native.Some (type_list, tv', v', tp', p')
                    ->
                    FStar_Reflection_V1_Derived.mk_app
                      (FStar_Reflection_V2_Builtins.pack_ln
                         (FStar_Reflection_V2_Data.Tv_UInst
                            ((FStar_Reflection_V2_Builtins.pack_fv
                                ["Steel";
                                "ST";
                                "GenElim1";
                                "Base";
                                "mk_gen_elim_nondep_by_tac"]),
                              [FStar_Reflection_V2_Builtins.pack_universe
                                 (FStar_Reflection_V2_Data.Uv_Succ
                                    (FStar_Reflection_V2_Builtins.pack_universe
                                       FStar_Reflection_V2_Data.Uv_Zero))])))
                      [(type_list, FStar_Reflection_V1_Data.Q_Explicit);
                      (tv', FStar_Reflection_V1_Data.Q_Explicit);
                      (v', FStar_Reflection_V1_Data.Q_Explicit);
                      (tp', FStar_Reflection_V1_Data.Q_Explicit);
                      (p', FStar_Reflection_V1_Data.Q_Explicit)]))
let (trefl_or_smt : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Steel.ST.GenElim1.Base.fsti"
               (Prims.of_int (623)) (Prims.of_int (11)) (Prims.of_int (623))
               (Prims.of_int (24)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Steel.ST.GenElim1.Base.fsti"
               (Prims.of_int (624)) (Prims.of_int (2)) (Prims.of_int (626))
               (Prims.of_int (27)))))
      (Obj.magic (FStar_Tactics_V1_Derived.cur_goal ()))
      (fun uu___1 ->
         (fun ty ->
            Obj.magic
              (FStar_Tactics_Effect.tac_bind
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "Steel.ST.GenElim1.Base.fsti"
                          (Prims.of_int (624)) (Prims.of_int (8))
                          (Prims.of_int (624)) (Prims.of_int (28)))))
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "Steel.ST.GenElim1.Base.fsti"
                          (Prims.of_int (624)) (Prims.of_int (2))
                          (Prims.of_int (626)) (Prims.of_int (27)))))
                 (Obj.magic (FStar_Reflection_V1_Formula.term_as_formula ty))
                 (fun uu___1 ->
                    (fun uu___1 ->
                       match uu___1 with
                       | FStar_Reflection_V1_Formula.Comp
                           (uu___2, uu___3, uu___4) ->
                           Obj.magic (FStar_Tactics_V1_Derived.trefl ())
                       | uu___2 ->
                           Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "Steel.ST.GenElim1.Base.fsti"
                                         (Prims.of_int (626))
                                         (Prims.of_int (9))
                                         (Prims.of_int (626))
                                         (Prims.of_int (17)))))
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "Steel.ST.GenElim1.Base.fsti"
                                         (Prims.of_int (626))
                                         (Prims.of_int (19))
                                         (Prims.of_int (626))
                                         (Prims.of_int (27)))))
                                (Obj.magic (FStar_Tactics_V1_Derived.smt ()))
                                (fun uu___3 ->
                                   (fun uu___3 ->
                                      Obj.magic
                                        (FStar_Tactics_V1_Derived.qed ()))
                                     uu___3))) uu___1))) uu___1)
let (solve_gen_elim_prop :
  unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Steel.ST.GenElim1.Base.fsti"
               (Prims.of_int (632)) (Prims.of_int (17)) (Prims.of_int (632))
               (Prims.of_int (46)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Steel.ST.GenElim1.Base.fsti"
               (Prims.of_int (631)) Prims.int_one (Prims.of_int (670))
               (Prims.of_int (35)))))
      (Obj.magic
         (FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Steel.ST.GenElim1.Base.fsti"
                     (Prims.of_int (632)) (Prims.of_int (31))
                     (Prims.of_int (632)) (Prims.of_int (46)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Steel.ST.GenElim1.Base.fsti"
                     (Prims.of_int (632)) (Prims.of_int (17))
                     (Prims.of_int (632)) (Prims.of_int (46)))))
            (Obj.magic (FStar_Tactics_V1_Derived.cur_goal ()))
            (fun uu___1 ->
               (fun uu___1 ->
                  Obj.magic
                    (FStar_Tactics_V1_SyntaxHelpers.collect_app uu___1))
                 uu___1)))
      (fun uu___1 ->
         (fun uu___1 ->
            match uu___1 with
            | (hd, tl) ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "Steel.ST.GenElim1.Base.fsti"
                              (Prims.of_int (633)) (Prims.of_int (2))
                              (Prims.of_int (634)) (Prims.of_int (33)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "Steel.ST.GenElim1.Base.fsti"
                              (Prims.of_int (635)) (Prims.of_int (2))
                              (Prims.of_int (670)) (Prims.of_int (35)))))
                     (Obj.magic
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "Steel.ST.GenElim1.Base.fsti"
                                    (Prims.of_int (633)) (Prims.of_int (5))
                                    (Prims.of_int (633)) (Prims.of_int (23)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "Steel.ST.GenElim1.Base.fsti"
                                    (Prims.of_int (633)) (Prims.of_int (2))
                                    (Prims.of_int (634)) (Prims.of_int (33)))))
                           (Obj.magic
                              (FStar_Tactics_Effect.tac_bind
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "Steel.ST.GenElim1.Base.fsti"
                                          (Prims.of_int (633))
                                          (Prims.of_int (9))
                                          (Prims.of_int (633))
                                          (Prims.of_int (23)))))
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "Steel.ST.GenElim1.Base.fsti"
                                          (Prims.of_int (633))
                                          (Prims.of_int (5))
                                          (Prims.of_int (633))
                                          (Prims.of_int (23)))))
                                 (Obj.magic (is_squash hd))
                                 (fun uu___2 ->
                                    FStar_Tactics_Effect.lift_div_tac
                                      (fun uu___3 -> Prims.op_Negation uu___2))))
                           (fun uu___2 ->
                              if uu___2
                              then
                                FStar_Tactics_V1_Derived.fail
                                  "not a squash goal"
                              else
                                FStar_Tactics_Effect.lift_div_tac
                                  (fun uu___4 -> ()))))
                     (fun uu___2 ->
                        (fun uu___2 ->
                           match tl with
                           | (body1, FStar_Reflection_V1_Data.Q_Explicit)::[]
                               ->
                               Obj.magic
                                 (Obj.repr
                                    (FStar_Tactics_Effect.tac_bind
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "Steel.ST.GenElim1.Base.fsti"
                                                (Prims.of_int (637))
                                                (Prims.of_int (21))
                                                (Prims.of_int (637))
                                                (Prims.of_int (40)))))
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "Steel.ST.GenElim1.Base.fsti"
                                                (Prims.of_int (636))
                                                (Prims.of_int (28))
                                                (Prims.of_int (669))
                                                (Prims.of_int (7)))))
                                       (Obj.magic
                                          (FStar_Tactics_V1_SyntaxHelpers.collect_app
                                             body1))
                                       (fun uu___3 ->
                                          (fun uu___3 ->
                                             match uu___3 with
                                             | (hd1, tl1) ->
                                                 Obj.magic
                                                   (FStar_Tactics_Effect.tac_bind
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "Steel.ST.GenElim1.Base.fsti"
                                                               (Prims.of_int (638))
                                                               (Prims.of_int (4))
                                                               (Prims.of_int (639))
                                                               (Prims.of_int (42)))))
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "Steel.ST.GenElim1.Base.fsti"
                                                               (Prims.of_int (640))
                                                               (Prims.of_int (10))
                                                               (Prims.of_int (668))
                                                               (Prims.of_int (44)))))
                                                      (if
                                                         Prims.op_Negation
                                                           (is_fvar hd1
                                                              "Steel.ST.GenElim1.Base.gen_elim_prop")
                                                       then
                                                         FStar_Tactics_V1_Derived.fail
                                                           "not a gen_elim_prop goal"
                                                       else
                                                         FStar_Tactics_Effect.lift_div_tac
                                                           (fun uu___5 -> ()))
                                                      (fun uu___4 ->
                                                         (fun uu___4 ->
                                                            match FStar_List_Tot_Base.filter
                                                                    (
                                                                    fun
                                                                    uu___5 ->
                                                                    match uu___5
                                                                    with
                                                                    | 
                                                                    (uu___6,
                                                                    x) ->
                                                                    FStar_Reflection_V1_Data.uu___is_Q_Explicit
                                                                    x) tl1
                                                            with
                                                            | (enable_nondep_opt_tm,
                                                               uu___5)::
                                                                (p, uu___6)::
                                                                (a, uu___7)::
                                                                (q, uu___8)::
                                                                (post,
                                                                 uu___9)::[]
                                                                ->
                                                                Obj.magic
                                                                  (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (642))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (642))
                                                                    (Prims.of_int (74)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (642))
                                                                    (Prims.of_int (77))
                                                                    (Prims.of_int (667))
                                                                    (Prims.of_int (44)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_V1_Builtins.term_eq_old
                                                                    enable_nondep_opt_tm
                                                                    (FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_Const
                                                                    FStar_Reflection_V2_Data.C_True))))
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun
                                                                    enable_nondep_opt
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (643))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (643))
                                                                    (Prims.of_int (31)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (643))
                                                                    (Prims.of_int (34))
                                                                    (Prims.of_int (667))
                                                                    (Prims.of_int (44)))))
                                                                    (Obj.magic
                                                                    (solve_gen_elim
                                                                    p))
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun i'
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (644))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (644))
                                                                    (Prims.of_int (73)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (645))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (667))
                                                                    (Prims.of_int (44)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    fun
                                                                    uu___11
                                                                    ->
                                                                    FStar_Tactics_V1_Builtins.norm
                                                                    [
                                                                    FStar_Pervasives.delta_attr
                                                                    ["Steel.ST.GenElim1.Base.gen_elim_reduce"];
                                                                    FStar_Pervasives.zeta;
                                                                    FStar_Pervasives.iota]))
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun norm
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (645))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (661))
                                                                    (Prims.of_int (46)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (663))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (667))
                                                                    (Prims.of_int (44)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (645))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (645))
                                                                    (Prims.of_int (61)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (645))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (661))
                                                                    (Prims.of_int (46)))))
                                                                    (Obj.magic
                                                                    (solve_gen_elim_nondep0
                                                                    enable_nondep_opt
                                                                    i'))
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    match uu___10
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_V1_Derived.apply_lemma
                                                                    (FStar_Reflection_V1_Derived.mk_app
                                                                    (FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_FVar
                                                                    (FStar_Reflection_V2_Builtins.pack_fv
                                                                    ["Steel";
                                                                    "ST";
                                                                    "GenElim1";
                                                                    "Base";
                                                                    "gen_elim_prop_intro'"])))
                                                                    [
                                                                    (i',
                                                                    FStar_Reflection_V1_Data.Q_Explicit);
                                                                    ((FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_FVar
                                                                    (FStar_Reflection_V2_Builtins.pack_fv
                                                                    ["Steel";
                                                                    "ST";
                                                                    "GenElim1";
                                                                    "Base";
                                                                    "GEDep"]))),
                                                                    FStar_Reflection_V1_Data.Q_Explicit)]))
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (type_list,
                                                                    tvprop,
                                                                    q0,
                                                                    tprop,
                                                                    post0) ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (652))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (659))
                                                                    (Prims.of_int (10)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (660))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (661))
                                                                    (Prims.of_int (46)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_V1_Derived.apply_lemma
                                                                    (FStar_Reflection_V1_Derived.mk_app
                                                                    (FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_FVar
                                                                    (FStar_Reflection_V2_Builtins.pack_fv
                                                                    ["Steel";
                                                                    "ST";
                                                                    "GenElim1";
                                                                    "Base";
                                                                    "gen_elim_prop_intro"])))
                                                                    [
                                                                    (i',
                                                                    FStar_Reflection_V1_Data.Q_Explicit);
                                                                    (type_list,
                                                                    FStar_Reflection_V1_Data.Q_Explicit);
                                                                    (tvprop,
                                                                    FStar_Reflection_V1_Data.Q_Explicit);
                                                                    (q0,
                                                                    FStar_Reflection_V1_Data.Q_Explicit);
                                                                    (tprop,
                                                                    FStar_Reflection_V1_Data.Q_Explicit);
                                                                    (post0,
                                                                    FStar_Reflection_V1_Data.Q_Explicit)])))
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (660))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (660))
                                                                    (Prims.of_int (46)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (661))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (661))
                                                                    (Prims.of_int (46)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_V1_Derived.focus
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (660))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (660))
                                                                    (Prims.of_int (33)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (660))
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (660))
                                                                    (Prims.of_int (45)))))
                                                                    (Obj.magic
                                                                    (norm ()))
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_V1_Derived.trefl
                                                                    ()))
                                                                    uu___13))))
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_V1_Derived.focus
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (661))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (661))
                                                                    (Prims.of_int (33)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (661))
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (661))
                                                                    (Prims.of_int (45)))))
                                                                    (Obj.magic
                                                                    (norm ()))
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_V1_Derived.trefl
                                                                    ()))
                                                                    uu___14))))
                                                                    uu___12)))
                                                                    uu___11)))
                                                                    uu___10)))
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (663))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (663))
                                                                    (Prims.of_int (44)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (664))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (667))
                                                                    (Prims.of_int (44)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_V1_Derived.focus
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (663))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (663))
                                                                    (Prims.of_int (31)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (663))
                                                                    (Prims.of_int (33))
                                                                    (Prims.of_int (663))
                                                                    (Prims.of_int (43)))))
                                                                    (Obj.magic
                                                                    (norm ()))
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_V1_Derived.trefl
                                                                    ()))
                                                                    uu___12))))
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (664))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (664))
                                                                    (Prims.of_int (49)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (665))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (667))
                                                                    (Prims.of_int (44)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_V1_Derived.focus
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (664))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (664))
                                                                    (Prims.of_int (31)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (664))
                                                                    (Prims.of_int (33))
                                                                    (Prims.of_int (664))
                                                                    (Prims.of_int (48)))))
                                                                    (Obj.magic
                                                                    (norm ()))
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    Obj.magic
                                                                    (trefl_or_smt
                                                                    ()))
                                                                    uu___13))))
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (665))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (665))
                                                                    (Prims.of_int (44)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (666))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (667))
                                                                    (Prims.of_int (44)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_V1_Derived.focus
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (665))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (665))
                                                                    (Prims.of_int (31)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (665))
                                                                    (Prims.of_int (33))
                                                                    (Prims.of_int (665))
                                                                    (Prims.of_int (43)))))
                                                                    (Obj.magic
                                                                    (norm ()))
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_V1_Derived.trefl
                                                                    ()))
                                                                    uu___14))))
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (666))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (666))
                                                                    (Prims.of_int (44)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (667))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (667))
                                                                    (Prims.of_int (44)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_V1_Derived.focus
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (666))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (666))
                                                                    (Prims.of_int (31)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (666))
                                                                    (Prims.of_int (33))
                                                                    (Prims.of_int (666))
                                                                    (Prims.of_int (43)))))
                                                                    (Obj.magic
                                                                    (norm ()))
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_V1_Derived.trefl
                                                                    ()))
                                                                    uu___15))))
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_V1_Derived.focus
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (667))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (667))
                                                                    (Prims.of_int (31)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (667))
                                                                    (Prims.of_int (33))
                                                                    (Prims.of_int (667))
                                                                    (Prims.of_int (43)))))
                                                                    (Obj.magic
                                                                    (norm ()))
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_V1_Derived.trefl
                                                                    ()))
                                                                    uu___16))))
                                                                    uu___14)))
                                                                    uu___13)))
                                                                    uu___12)))
                                                                    uu___11)))
                                                                    uu___10)))
                                                                    uu___10)))
                                                                    uu___10)))
                                                                    uu___10)))
                                                            | uu___5 ->
                                                                Obj.magic
                                                                  (Obj.repr
                                                                    (FStar_Tactics_V1_Derived.fail
                                                                    "ill formed gen_elim_prop")))
                                                           uu___4))) uu___3)))
                           | uu___3 ->
                               Obj.magic
                                 (Obj.repr
                                    (FStar_Tactics_V1_Derived.fail
                                       "ill-formed squash"))) uu___2)))
           uu___1)
let (solve_gen_elim_prop_placeholder :
  unit -> (Prims.bool, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Steel.ST.GenElim1.Base.fsti"
               (Prims.of_int (676)) (Prims.of_int (17)) (Prims.of_int (676))
               (Prims.of_int (46)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "Steel.ST.GenElim1.Base.fsti"
               (Prims.of_int (675)) Prims.int_one (Prims.of_int (712))
               (Prims.of_int (35)))))
      (Obj.magic
         (FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Steel.ST.GenElim1.Base.fsti"
                     (Prims.of_int (676)) (Prims.of_int (31))
                     (Prims.of_int (676)) (Prims.of_int (46)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "Steel.ST.GenElim1.Base.fsti"
                     (Prims.of_int (676)) (Prims.of_int (17))
                     (Prims.of_int (676)) (Prims.of_int (46)))))
            (Obj.magic (FStar_Tactics_V1_Derived.cur_goal ()))
            (fun uu___1 ->
               (fun uu___1 ->
                  Obj.magic
                    (FStar_Tactics_V1_SyntaxHelpers.collect_app uu___1))
                 uu___1)))
      (fun uu___1 ->
         (fun uu___1 ->
            match uu___1 with
            | (hd, tl) ->
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "Steel.ST.GenElim1.Base.fsti"
                              (Prims.of_int (677)) (Prims.of_int (2))
                              (Prims.of_int (678)) (Prims.of_int (33)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "Steel.ST.GenElim1.Base.fsti"
                              (Prims.of_int (679)) (Prims.of_int (2))
                              (Prims.of_int (712)) (Prims.of_int (35)))))
                     (Obj.magic
                        (FStar_Tactics_Effect.tac_bind
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "Steel.ST.GenElim1.Base.fsti"
                                    (Prims.of_int (677)) (Prims.of_int (5))
                                    (Prims.of_int (677)) (Prims.of_int (23)))))
                           (FStar_Sealed.seal
                              (Obj.magic
                                 (FStar_Range.mk_range
                                    "Steel.ST.GenElim1.Base.fsti"
                                    (Prims.of_int (677)) (Prims.of_int (2))
                                    (Prims.of_int (678)) (Prims.of_int (33)))))
                           (Obj.magic
                              (FStar_Tactics_Effect.tac_bind
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "Steel.ST.GenElim1.Base.fsti"
                                          (Prims.of_int (677))
                                          (Prims.of_int (9))
                                          (Prims.of_int (677))
                                          (Prims.of_int (23)))))
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "Steel.ST.GenElim1.Base.fsti"
                                          (Prims.of_int (677))
                                          (Prims.of_int (5))
                                          (Prims.of_int (677))
                                          (Prims.of_int (23)))))
                                 (Obj.magic (is_squash hd))
                                 (fun uu___2 ->
                                    FStar_Tactics_Effect.lift_div_tac
                                      (fun uu___3 -> Prims.op_Negation uu___2))))
                           (fun uu___2 ->
                              if uu___2
                              then
                                FStar_Tactics_V1_Derived.fail
                                  "not a squash goal"
                              else
                                FStar_Tactics_Effect.lift_div_tac
                                  (fun uu___4 -> ()))))
                     (fun uu___2 ->
                        (fun uu___2 ->
                           match tl with
                           | (body1, FStar_Reflection_V1_Data.Q_Explicit)::[]
                               ->
                               Obj.magic
                                 (Obj.repr
                                    (FStar_Tactics_Effect.tac_bind
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "Steel.ST.GenElim1.Base.fsti"
                                                (Prims.of_int (681))
                                                (Prims.of_int (21))
                                                (Prims.of_int (681))
                                                (Prims.of_int (40)))))
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "Steel.ST.GenElim1.Base.fsti"
                                                (Prims.of_int (680))
                                                (Prims.of_int (28))
                                                (Prims.of_int (711))
                                                (Prims.of_int (7)))))
                                       (Obj.magic
                                          (FStar_Tactics_V1_SyntaxHelpers.collect_app
                                             body1))
                                       (fun uu___3 ->
                                          (fun uu___3 ->
                                             match uu___3 with
                                             | (hd1, tl1) ->
                                                 Obj.magic
                                                   (FStar_Tactics_Effect.tac_bind
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "Steel.ST.GenElim1.Base.fsti"
                                                               (Prims.of_int (682))
                                                               (Prims.of_int (4))
                                                               (Prims.of_int (683))
                                                               (Prims.of_int (54)))))
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "Steel.ST.GenElim1.Base.fsti"
                                                               (Prims.of_int (684))
                                                               (Prims.of_int (10))
                                                               (Prims.of_int (710))
                                                               (Prims.of_int (56)))))
                                                      (if
                                                         Prims.op_Negation
                                                           (is_fvar hd1
                                                              "Steel.ST.GenElim1.Base.gen_elim_prop_placeholder")
                                                       then
                                                         FStar_Tactics_V1_Derived.fail
                                                           "not a gen_elim_prop_placeholder goal"
                                                       else
                                                         FStar_Tactics_Effect.lift_div_tac
                                                           (fun uu___5 -> ()))
                                                      (fun uu___4 ->
                                                         (fun uu___4 ->
                                                            match FStar_List_Tot_Base.filter
                                                                    (
                                                                    fun
                                                                    uu___5 ->
                                                                    match uu___5
                                                                    with
                                                                    | 
                                                                    (uu___6,
                                                                    x) ->
                                                                    FStar_Reflection_V1_Data.uu___is_Q_Explicit
                                                                    x) tl1
                                                            with
                                                            | (enable_nondep_opt_tm,
                                                               uu___5)::
                                                                (p, uu___6)::
                                                                (a, uu___7)::
                                                                (q, uu___8)::
                                                                (post,
                                                                 uu___9)::[]
                                                                ->
                                                                Obj.magic
                                                                  (Obj.repr
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (686))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (687))
                                                                    (Prims.of_int (47)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (687))
                                                                    (Prims.of_int (48))
                                                                    (Prims.of_int (709))
                                                                    (Prims.of_int (10)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (686))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (686))
                                                                    (Prims.of_int (32)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (686))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (687))
                                                                    (Prims.of_int (47)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (686))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (686))
                                                                    (Prims.of_int (27)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (686))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (686))
                                                                    (Prims.of_int (32)))))
                                                                    (Obj.magic
                                                                    (Steel_Effect_Common.slterm_nbr_uvars
                                                                    p))
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    uu___10
                                                                    <>
                                                                    Prims.int_zero))))
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    if
                                                                    uu___10
                                                                    then
                                                                    FStar_Tactics_V1_Derived.fail
                                                                    "pre-resource not solved yet"
                                                                    else
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___12
                                                                    -> ()))))
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (688))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (688))
                                                                    (Prims.of_int (46)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (688))
                                                                    (Prims.of_int (49))
                                                                    (Prims.of_int (709))
                                                                    (Prims.of_int (10)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (688))
                                                                    (Prims.of_int (33))
                                                                    (Prims.of_int (688))
                                                                    (Prims.of_int (46)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (688))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (688))
                                                                    (Prims.of_int (46)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_V1_Builtins.inspect
                                                                    a))
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    FStar_Reflection_V1_Data.uu___is_Tv_Uvar
                                                                    uu___11))))
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    (fun
                                                                    a_is_uvar
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (689))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (689))
                                                                    (Prims.of_int (46)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (689))
                                                                    (Prims.of_int (49))
                                                                    (Prims.of_int (709))
                                                                    (Prims.of_int (10)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (689))
                                                                    (Prims.of_int (33))
                                                                    (Prims.of_int (689))
                                                                    (Prims.of_int (46)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (689))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (689))
                                                                    (Prims.of_int (46)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_V1_Builtins.inspect
                                                                    q))
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    FStar_Reflection_V1_Data.uu___is_Tv_Uvar
                                                                    uu___11))))
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    (fun
                                                                    q_is_uvar
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (690))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (690))
                                                                    (Prims.of_int (52)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (691))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (709))
                                                                    (Prims.of_int (10)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (690))
                                                                    (Prims.of_int (36))
                                                                    (Prims.of_int (690))
                                                                    (Prims.of_int (52)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (690))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (690))
                                                                    (Prims.of_int (52)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_V1_Builtins.inspect
                                                                    post))
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    FStar_Reflection_V1_Data.uu___is_Tv_Uvar
                                                                    uu___11))))
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    (fun
                                                                    post_is_uvar
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (691))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (692))
                                                                    (Prims.of_int (63)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (692))
                                                                    (Prims.of_int (64))
                                                                    (Prims.of_int (709))
                                                                    (Prims.of_int (10)))))
                                                                    (if
                                                                    Prims.op_Negation
                                                                    ((a_is_uvar
                                                                    &&
                                                                    q_is_uvar)
                                                                    &&
                                                                    post_is_uvar)
                                                                    then
                                                                    FStar_Tactics_V1_Derived.fail
                                                                    "gen_elim_prop_placeholder is already solved"
                                                                    else
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___12
                                                                    -> ()))
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (693))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (693))
                                                                    (Prims.of_int (74)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (693))
                                                                    (Prims.of_int (77))
                                                                    (Prims.of_int (709))
                                                                    (Prims.of_int (10)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_V1_Builtins.term_eq_old
                                                                    enable_nondep_opt_tm
                                                                    (FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_Const
                                                                    FStar_Reflection_V2_Data.C_True))))
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    (fun
                                                                    enable_nondep_opt
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (694))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (694))
                                                                    (Prims.of_int (31)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (694))
                                                                    (Prims.of_int (34))
                                                                    (Prims.of_int (709))
                                                                    (Prims.of_int (10)))))
                                                                    (Obj.magic
                                                                    (solve_gen_elim
                                                                    p))
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    (fun i'
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (695))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (695))
                                                                    (Prims.of_int (57)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (695))
                                                                    (Prims.of_int (60))
                                                                    (Prims.of_int (709))
                                                                    (Prims.of_int (10)))))
                                                                    (Obj.magic
                                                                    (solve_gen_elim_nondep
                                                                    enable_nondep_opt
                                                                    i'))
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    (fun j'
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (696))
                                                                    (Prims.of_int (22))
                                                                    (Prims.of_int (696))
                                                                    (Prims.of_int (80)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (696))
                                                                    (Prims.of_int (83))
                                                                    (Prims.of_int (709))
                                                                    (Prims.of_int (10)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    FStar_Tactics_V1_Derived.norm_term
                                                                    [
                                                                    FStar_Pervasives.delta_attr
                                                                    ["Steel.ST.GenElim1.Base.gen_elim_reduce"];
                                                                    FStar_Pervasives.zeta;
                                                                    FStar_Pervasives.iota]))
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    (fun
                                                                    norm_term
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (697))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (697))
                                                                    (Prims.of_int (89)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (697))
                                                                    (Prims.of_int (92))
                                                                    (Prims.of_int (709))
                                                                    (Prims.of_int (10)))))
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    FStar_Reflection_V1_Derived.mk_app
                                                                    (FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_FVar
                                                                    (FStar_Reflection_V2_Builtins.pack_fv
                                                                    ["Steel";
                                                                    "ST";
                                                                    "GenElim1";
                                                                    "Base";
                                                                    "compute_gen_elim_nondep_a"])))
                                                                    [
                                                                    (i',
                                                                    FStar_Reflection_V1_Data.Q_Explicit);
                                                                    (j',
                                                                    FStar_Reflection_V1_Data.Q_Explicit)]))
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    (fun a'
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (698))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (698))
                                                                    (Prims.of_int (37)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (698))
                                                                    (Prims.of_int (40))
                                                                    (Prims.of_int (709))
                                                                    (Prims.of_int (10)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_V1_Builtins.term_to_string
                                                                    a'))
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    (fun
                                                                    a'_ts ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (699))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (699))
                                                                    (Prims.of_int (27)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (699))
                                                                    (Prims.of_int (30))
                                                                    (Prims.of_int (709))
                                                                    (Prims.of_int (10)))))
                                                                    (Obj.magic
                                                                    (norm_term
                                                                    a'))
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    (fun a'1
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (700))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (700))
                                                                    (Prims.of_int (101)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (700))
                                                                    (Prims.of_int (104))
                                                                    (Prims.of_int (709))
                                                                    (Prims.of_int (10)))))
                                                                    (Obj.magic
                                                                    (norm_term
                                                                    (FStar_Reflection_V1_Derived.mk_app
                                                                    (FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_FVar
                                                                    (FStar_Reflection_V2_Builtins.pack_fv
                                                                    ["Steel";
                                                                    "ST";
                                                                    "GenElim1";
                                                                    "Base";
                                                                    "compute_gen_elim_nondep_q"])))
                                                                    [
                                                                    (i',
                                                                    FStar_Reflection_V1_Data.Q_Explicit);
                                                                    (j',
                                                                    FStar_Reflection_V1_Data.Q_Explicit)])))
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    (fun q'
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (701))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (701))
                                                                    (Prims.of_int (107)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (702))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (709))
                                                                    (Prims.of_int (10)))))
                                                                    (Obj.magic
                                                                    (norm_term
                                                                    (FStar_Reflection_V1_Derived.mk_app
                                                                    (FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_FVar
                                                                    (FStar_Reflection_V2_Builtins.pack_fv
                                                                    ["Steel";
                                                                    "ST";
                                                                    "GenElim1";
                                                                    "Base";
                                                                    "compute_gen_elim_nondep_post"])))
                                                                    [
                                                                    (i',
                                                                    FStar_Reflection_V1_Data.Q_Explicit);
                                                                    (j',
                                                                    FStar_Reflection_V1_Data.Q_Explicit)])))
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    (fun
                                                                    post' ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (702))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (702))
                                                                    (Prims.of_int (18)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (703))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (709))
                                                                    (Prims.of_int (10)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_V1_Builtins.unshelve
                                                                    a))
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (703))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (703))
                                                                    (Prims.of_int (16)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (704))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (709))
                                                                    (Prims.of_int (10)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_V1_Derived.exact
                                                                    a'1))
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (704))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (704))
                                                                    (Prims.of_int (18)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (705))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (709))
                                                                    (Prims.of_int (10)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_V1_Builtins.unshelve
                                                                    q))
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (705))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (705))
                                                                    (Prims.of_int (16)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (706))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (709))
                                                                    (Prims.of_int (10)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_V1_Derived.exact
                                                                    q'))
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (706))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (706))
                                                                    (Prims.of_int (21)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (707))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (709))
                                                                    (Prims.of_int (10)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_V1_Builtins.unshelve
                                                                    post))
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (707))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (707))
                                                                    (Prims.of_int (19)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (708))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (709))
                                                                    (Prims.of_int (10)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_V1_Derived.exact
                                                                    post'))
                                                                    (fun
                                                                    uu___17
                                                                    ->
                                                                    (fun
                                                                    uu___17
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (708))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (708))
                                                                    (Prims.of_int (54)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Steel.ST.GenElim1.Base.fsti"
                                                                    (Prims.of_int (709))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (709))
                                                                    (Prims.of_int (10)))))
                                                                    (Obj.magic
                                                                    (FStar_Tactics_V1_Derived.apply_lemma
                                                                    (FStar_Reflection_V2_Builtins.pack_ln
                                                                    (FStar_Reflection_V2_Data.Tv_FVar
                                                                    (FStar_Reflection_V2_Builtins.pack_fv
                                                                    ["Steel";
                                                                    "ST";
                                                                    "GenElim1";
                                                                    "Base";
                                                                    "gen_elim_prop_placeholder_intro"])))))
                                                                    (fun
                                                                    uu___18
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___19
                                                                    -> true))))
                                                                    uu___17)))
                                                                    uu___16)))
                                                                    uu___15)))
                                                                    uu___14)))
                                                                    uu___13)))
                                                                    uu___12)))
                                                                    uu___12)))
                                                                    uu___12)))
                                                                    uu___12)))
                                                                    uu___12)))
                                                                    uu___12)))
                                                                    uu___12)))
                                                                    uu___12)))
                                                                    uu___12)))
                                                                    uu___12)))
                                                                    uu___11)))
                                                                    uu___11)))
                                                                    uu___11)))
                                                                    uu___11)))
                                                                    uu___10)))
                                                            | uu___5 ->
                                                                Obj.magic
                                                                  (Obj.repr
                                                                    (FStar_Tactics_V1_Derived.fail
                                                                    "ill-formed gen_elim_prop_placeholder")))
                                                           uu___4))) uu___3)))
                           | uu___3 ->
                               Obj.magic
                                 (Obj.repr
                                    (FStar_Tactics_V1_Derived.fail
                                       "ill-formed squash"))) uu___2)))
           uu___1)
let (init_resolve_tac : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    Steel_Effect_Common.init_resolve_tac'
      [((FStar_Reflection_V2_Builtins.pack_ln
           (FStar_Reflection_V2_Data.Tv_FVar
              (FStar_Reflection_V2_Builtins.pack_fv
                 ["Steel";
                 "ST";
                 "GenElim1";
                 "Base";
                 "gen_elim_prop_placeholder"]))),
         solve_gen_elim_prop_placeholder)]
let _ =
  FStar_Tactics_Native.register_tactic
    "Steel.ST.GenElim1.Base.init_resolve_tac" (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun args ->
           FStar_Tactics_V2_InterpFuns.mk_tactic_interpretation_1
             "Steel.ST.GenElim1.Base.init_resolve_tac (plugin)"
             (FStar_Tactics_Native.from_tactic_1 init_resolve_tac)
             FStar_Syntax_Embeddings.e_unit FStar_Syntax_Embeddings.e_unit
             psc ncb args)