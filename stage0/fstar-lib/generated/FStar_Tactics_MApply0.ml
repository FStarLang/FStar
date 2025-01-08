open Prims
let rec (apply_squash_or_lem :
  Prims.nat ->
    FStar_Tactics_NamedView.term ->
      (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun d ->
    fun t ->
      FStar_Tactics_V2_Derived.try_with
        (fun uu___ -> match () with | () -> FStar_Tactics_V2_Derived.apply t)
        (fun uu___ ->
           FStar_Tactics_V2_Derived.try_with
             (fun uu___1 ->
                match () with
                | () ->
                    let uu___2 =
                      FStar_Tactics_V2_Derived.apply
                        (FStarC_Reflection_V2_Builtins.pack_ln
                           (FStarC_Reflection_V2_Data.Tv_FVar
                              (FStarC_Reflection_V2_Builtins.pack_fv
                                 ["FStar"; "Squash"; "return_squash"]))) in
                    FStar_Tactics_Effect.tac_bind
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range "FStar.Tactics.MApply0.fst"
                               (Prims.of_int (24)) (Prims.of_int (8))
                               (Prims.of_int (24)) (Prims.of_int (43)))))
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range "FStar.Tactics.MApply0.fst"
                               (Prims.of_int (24)) (Prims.of_int (45))
                               (Prims.of_int (24)) (Prims.of_int (52)))))
                      (Obj.magic uu___2)
                      (fun uu___3 ->
                         (fun uu___3 ->
                            Obj.magic (FStar_Tactics_V2_Derived.apply t))
                           uu___3))
             (fun uu___1 ->
                FStar_Tactics_V2_Derived.try_with
                  (fun uu___2 ->
                     match () with
                     | () -> FStar_Tactics_V2_Derived.apply_lemma t)
                  (fun uu___2 ->
                     (fun uu___2 ->
                        if d <= Prims.int_zero
                        then
                          Obj.magic
                            (Obj.repr
                               (FStar_Tactics_V2_Derived.fail
                                  "mapply: out of fuel"))
                        else
                          Obj.magic
                            (Obj.repr
                               (let uu___4 =
                                  let uu___5 =
                                    FStar_Tactics_V2_Derived.cur_env () in
                                  FStar_Tactics_Effect.tac_bind
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "FStar.Tactics.MApply0.fst"
                                             (Prims.of_int (30))
                                             (Prims.of_int (16))
                                             (Prims.of_int (30))
                                             (Prims.of_int (28)))))
                                    (FStar_Sealed.seal
                                       (Obj.magic
                                          (FStar_Range.mk_range
                                             "FStar.Tactics.MApply0.fst"
                                             (Prims.of_int (30))
                                             (Prims.of_int (13))
                                             (Prims.of_int (30))
                                             (Prims.of_int (30)))))
                                    (Obj.magic uu___5)
                                    (fun uu___6 ->
                                       (fun uu___6 ->
                                          Obj.magic
                                            (FStarC_Tactics_V2_Builtins.tc
                                               uu___6 t)) uu___6) in
                                FStar_Tactics_Effect.tac_bind
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "FStar.Tactics.MApply0.fst"
                                           (Prims.of_int (30))
                                           (Prims.of_int (13))
                                           (Prims.of_int (30))
                                           (Prims.of_int (30)))))
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "FStar.Tactics.MApply0.fst"
                                           (Prims.of_int (30))
                                           (Prims.of_int (33))
                                           (Prims.of_int (79))
                                           (Prims.of_int (41)))))
                                  (Obj.magic uu___4)
                                  (fun uu___5 ->
                                     (fun ty ->
                                        let uu___5 =
                                          FStar_Tactics_V2_SyntaxHelpers.collect_arr
                                            ty in
                                        Obj.magic
                                          (FStar_Tactics_Effect.tac_bind
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "FStar.Tactics.MApply0.fst"
                                                      (Prims.of_int (31))
                                                      (Prims.of_int (17))
                                                      (Prims.of_int (31))
                                                      (Prims.of_int (31)))))
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "FStar.Tactics.MApply0.fst"
                                                      (Prims.of_int (30))
                                                      (Prims.of_int (33))
                                                      (Prims.of_int (79))
                                                      (Prims.of_int (41)))))
                                             (Obj.magic uu___5)
                                             (fun uu___6 ->
                                                (fun uu___6 ->
                                                   match uu___6 with
                                                   | (tys, c) ->
                                                       (match FStar_Tactics_NamedView.inspect_comp
                                                                c
                                                        with
                                                        | FStarC_Reflection_V2_Data.C_Lemma
                                                            (pre, post,
                                                             uu___7)
                                                            ->
                                                            Obj.magic
                                                              (Obj.repr
                                                                 (let uu___8
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_App
                                                                    (post,
                                                                    ((FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_Const
                                                                    FStarC_Reflection_V2_Data.C_Unit)),
                                                                    FStarC_Reflection_V2_Data.Q_Explicit))))) in
                                                                  FStar_Tactics_Effect.tac_bind
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MApply0.fst"
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (32)))))
                                                                    (
                                                                    FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MApply0.fst"
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (44))
                                                                    (Prims.of_int (41)))))
                                                                    (
                                                                    Obj.magic
                                                                    uu___8)
                                                                    (
                                                                    fun
                                                                    uu___9 ->
                                                                    (fun
                                                                    post1 ->
                                                                    let uu___9
                                                                    =
                                                                    FStar_Tactics_V2_Derived.norm_term
                                                                    [] post1 in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MApply0.fst"
                                                                    (Prims.of_int (36))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (36))
                                                                    (Prims.of_int (35)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MApply0.fst"
                                                                    (Prims.of_int (38))
                                                                    (Prims.of_int (7))
                                                                    (Prims.of_int (44))
                                                                    (Prims.of_int (41)))))
                                                                    (Obj.magic
                                                                    uu___9)
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun
                                                                    post2 ->
                                                                    let uu___10
                                                                    =
                                                                    FStar_Reflection_V2_Formula.term_as_formula'
                                                                    post2 in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MApply0.fst"
                                                                    (Prims.of_int (38))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (38))
                                                                    (Prims.of_int (34)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MApply0.fst"
                                                                    (Prims.of_int (38))
                                                                    (Prims.of_int (7))
                                                                    (Prims.of_int (44))
                                                                    (Prims.of_int (41)))))
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
                                                                    FStar_Reflection_V2_Formula.Implies
                                                                    (p, q) ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (let uu___12
                                                                    =
                                                                    FStar_Tactics_V2_Derived.apply_lemma
                                                                    (FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_FVar
                                                                    (FStarC_Reflection_V2_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "MApply0";
                                                                    "push1"]))) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MApply0.fst"
                                                                    (Prims.of_int (40))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (40))
                                                                    (Prims.of_int (31)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MApply0.fst"
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (38)))))
                                                                    (Obj.magic
                                                                    uu___12)
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    Obj.magic
                                                                    (apply_squash_or_lem
                                                                    (d -
                                                                    Prims.int_one)
                                                                    t))
                                                                    uu___13)))
                                                                    | 
                                                                    uu___12
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_V2_Derived.fail
                                                                    "mapply: can't apply (1)")))
                                                                    uu___11)))
                                                                    uu___10)))
                                                                    uu___9)))
                                                        | FStarC_Reflection_V2_Data.C_Total
                                                            rt ->
                                                            Obj.magic
                                                              (Obj.repr
                                                                 (match 
                                                                    FStar_Reflection_V2_Derived.unsquash_term
                                                                    rt
                                                                  with
                                                                  | FStar_Pervasives_Native.Some
                                                                    rt1 ->
                                                                    let uu___7
                                                                    =
                                                                    FStar_Tactics_V2_Derived.norm_term
                                                                    [] rt1 in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MApply0.fst"
                                                                    (Prims.of_int (52))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (52))
                                                                    (Prims.of_int (33)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MApply0.fst"
                                                                    (Prims.of_int (54))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (60))
                                                                    (Prims.of_int (43)))))
                                                                    (Obj.magic
                                                                    uu___7)
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun rt2
                                                                    ->
                                                                    let uu___8
                                                                    =
                                                                    FStar_Reflection_V2_Formula.term_as_formula'
                                                                    rt2 in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MApply0.fst"
                                                                    (Prims.of_int (54))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (54))
                                                                    (Prims.of_int (34)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MApply0.fst"
                                                                    (Prims.of_int (54))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (60))
                                                                    (Prims.of_int (43)))))
                                                                    (Obj.magic
                                                                    uu___8)
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun
                                                                    uu___9 ->
                                                                    match uu___9
                                                                    with
                                                                    | 
                                                                    FStar_Reflection_V2_Formula.Implies
                                                                    (p, q) ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (let uu___10
                                                                    =
                                                                    FStar_Tactics_V2_Derived.apply_lemma
                                                                    (FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_FVar
                                                                    (FStarC_Reflection_V2_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "MApply0";
                                                                    "push1"]))) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MApply0.fst"
                                                                    (Prims.of_int (56))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (56))
                                                                    (Prims.of_int (33)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MApply0.fst"
                                                                    (Prims.of_int (57))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (57))
                                                                    (Prims.of_int (40)))))
                                                                    (Obj.magic
                                                                    uu___10)
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    Obj.magic
                                                                    (apply_squash_or_lem
                                                                    (d -
                                                                    Prims.int_one)
                                                                    t))
                                                                    uu___11)))
                                                                    | 
                                                                    uu___10
                                                                    ->
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_V2_Derived.fail
                                                                    "mapply: can't apply (2)")))
                                                                    uu___9)))
                                                                    uu___8)
                                                                  | FStar_Pervasives_Native.None
                                                                    ->
                                                                    let uu___7
                                                                    =
                                                                    FStar_Tactics_V2_Derived.norm_term
                                                                    [] rt in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MApply0.fst"
                                                                    (Prims.of_int (67))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (67))
                                                                    (Prims.of_int (33)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MApply0.fst"
                                                                    (Prims.of_int (69))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (76))
                                                                    (Prims.of_int (20)))))
                                                                    (Obj.magic
                                                                    uu___7)
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun rt1
                                                                    ->
                                                                    let uu___8
                                                                    =
                                                                    FStar_Reflection_V2_Formula.term_as_formula'
                                                                    rt1 in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MApply0.fst"
                                                                    (Prims.of_int (69))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (69))
                                                                    (Prims.of_int (34)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MApply0.fst"
                                                                    (Prims.of_int (69))
                                                                    (Prims.of_int (9))
                                                                    (Prims.of_int (76))
                                                                    (Prims.of_int (20)))))
                                                                    (Obj.magic
                                                                    uu___8)
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun
                                                                    uu___9 ->
                                                                    match uu___9
                                                                    with
                                                                    | 
                                                                    FStar_Reflection_V2_Formula.Implies
                                                                    (p, q) ->
                                                                    let uu___10
                                                                    =
                                                                    FStar_Tactics_V2_Derived.apply_lemma
                                                                    (FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_FVar
                                                                    (FStarC_Reflection_V2_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "MApply0";
                                                                    "push1"]))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MApply0.fst"
                                                                    (Prims.of_int (71))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (71))
                                                                    (Prims.of_int (33)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MApply0.fst"
                                                                    (Prims.of_int (72))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (72))
                                                                    (Prims.of_int (40)))))
                                                                    (Obj.magic
                                                                    uu___10)
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    Obj.magic
                                                                    (apply_squash_or_lem
                                                                    (d -
                                                                    Prims.int_one)
                                                                    t))
                                                                    uu___11))
                                                                    | 
                                                                    uu___10
                                                                    ->
                                                                    let uu___11
                                                                    =
                                                                    FStar_Tactics_V2_Derived.apply
                                                                    (FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_FVar
                                                                    (FStarC_Reflection_V2_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Squash";
                                                                    "return_squash"]))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MApply0.fst"
                                                                    (Prims.of_int (75))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (75))
                                                                    (Prims.of_int (48)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MApply0.fst"
                                                                    (Prims.of_int (76))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (76))
                                                                    (Prims.of_int (20)))))
                                                                    (Obj.magic
                                                                    uu___11)
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_V2_Derived.apply
                                                                    t))
                                                                    uu___12)))
                                                                    uu___9)))
                                                                    uu___8)))
                                                        | uu___7 ->
                                                            Obj.magic
                                                              (Obj.repr
                                                                 (FStar_Tactics_V2_Derived.fail
                                                                    "mapply: can't apply (3)"))))
                                                  uu___6))) uu___5)))) uu___2)))
let (mapply0 :
  FStar_Tactics_NamedView.term -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  = fun t -> apply_squash_or_lem (Prims.of_int (10)) t
let _ =
  FStarC_Tactics_Native.register_tactic "FStar.Tactics.MApply0.mapply0"
    (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.MApply0.mapply0 (plugin)"
               (FStarC_Tactics_Native.from_tactic_1 mapply0)
               FStarC_Reflection_V2_Embeddings.e_term
               FStarC_Syntax_Embeddings.e_unit psc ncb us args)