open Prims
let (empty_elim : Prims.empty -> unit -> Obj.t) =
  fun uu___1 ->
    fun uu___ ->
      (fun e -> fun a -> Obj.magic (failwith "unreachable")) uu___1 uu___
let (add_suffix :
  Prims.string ->
    FStarC_Reflection_Types.name -> FStarC_Reflection_Types.name)
  =
  fun s ->
    fun nm ->
      FStarC_Reflection_V2_Builtins.explode_qn
        (Prims.strcat (FStarC_Reflection_V2_Builtins.implode_qn nm) s)
let (unitv_ : FStar_Tactics_NamedView.term) =
  FStarC_Reflection_V2_Builtins.pack_ln
    (FStarC_Reflection_V2_Data.Tv_Const FStarC_Reflection_V2_Data.C_Unit)
let (unitt_ : FStar_Tactics_NamedView.term) =
  FStarC_Reflection_V2_Builtins.pack_ln
    (FStarC_Reflection_V2_Data.Tv_FVar
       (FStarC_Reflection_V2_Builtins.pack_fv ["Prims"; "unit"]))
let (empty_ : FStar_Tactics_NamedView.term) =
  FStarC_Reflection_V2_Builtins.pack_ln
    (FStarC_Reflection_V2_Data.Tv_FVar
       (FStarC_Reflection_V2_Builtins.pack_fv ["Prims"; "empty"]))
let (either_ :
  FStar_Tactics_NamedView.term ->
    FStar_Tactics_NamedView.term -> FStar_Tactics_NamedView.term)
  =
  fun a ->
    fun b ->
      FStarC_Reflection_V2_Builtins.pack_ln
        (FStarC_Reflection_V2_Data.Tv_App
           ((FStarC_Reflection_V2_Builtins.pack_ln
               (FStarC_Reflection_V2_Data.Tv_App
                  ((FStarC_Reflection_V2_Builtins.pack_ln
                      (FStarC_Reflection_V2_Data.Tv_FVar
                         (FStarC_Reflection_V2_Builtins.pack_fv
                            ["FStar"; "Pervasives"; "either"]))),
                    (a, FStarC_Reflection_V2_Data.Q_Explicit)))),
             (b, FStarC_Reflection_V2_Data.Q_Explicit)))
let (tuple2_ :
  FStar_Tactics_NamedView.term ->
    FStar_Tactics_NamedView.term -> FStar_Tactics_NamedView.term)
  =
  fun a ->
    fun b ->
      FStarC_Reflection_V2_Builtins.pack_ln
        (FStarC_Reflection_V2_Data.Tv_App
           ((FStarC_Reflection_V2_Builtins.pack_ln
               (FStarC_Reflection_V2_Data.Tv_App
                  ((FStarC_Reflection_V2_Builtins.pack_ln
                      (FStarC_Reflection_V2_Data.Tv_FVar
                         (FStarC_Reflection_V2_Builtins.pack_fv
                            ["FStar"; "Pervasives"; "Native"; "tuple2"]))),
                    (a, FStarC_Reflection_V2_Data.Q_Explicit)))),
             (b, FStarC_Reflection_V2_Data.Q_Explicit)))
let (mktuple2_ :
  FStar_Tactics_NamedView.term ->
    FStar_Tactics_NamedView.term -> FStar_Tactics_NamedView.term)
  =
  fun a ->
    fun b ->
      FStarC_Reflection_V2_Builtins.pack_ln
        (FStarC_Reflection_V2_Data.Tv_App
           ((FStarC_Reflection_V2_Builtins.pack_ln
               (FStarC_Reflection_V2_Data.Tv_App
                  ((FStarC_Reflection_V2_Builtins.pack_ln
                      (FStarC_Reflection_V2_Data.Tv_FVar
                         (FStarC_Reflection_V2_Builtins.pack_fv
                            ["FStar"; "Pervasives"; "Native"; "Mktuple2"]))),
                    (a, FStarC_Reflection_V2_Data.Q_Explicit)))),
             (b, FStarC_Reflection_V2_Data.Q_Explicit)))
let (get_inductive_typ :
  Prims.string ->
    (FStar_Tactics_NamedView.sigelt_view, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun nm ->
    let uu___ = FStarC_Tactics_V2_Builtins.top_env () in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.TypeRepr.fst"
               (Prims.of_int (18)) (Prims.of_int (10)) (Prims.of_int (18))
               (Prims.of_int (20)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.TypeRepr.fst"
               (Prims.of_int (18)) (Prims.of_int (23)) (Prims.of_int (27))
               (Prims.of_int (48))))) (Obj.magic uu___)
      (fun uu___1 ->
         (fun e ->
            let uu___1 =
              Obj.magic
                (FStar_Tactics_Effect.lift_div_tac
                   (fun uu___2 ->
                      FStarC_Reflection_V2_Builtins.lookup_typ e
                        (FStarC_Reflection_V2_Builtins.explode_qn nm))) in
            Obj.magic
              (FStar_Tactics_Effect.tac_bind
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "FStar.Tactics.TypeRepr.fst"
                          (Prims.of_int (19)) (Prims.of_int (11))
                          (Prims.of_int (19)) (Prims.of_int (39)))))
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "FStar.Tactics.TypeRepr.fst"
                          (Prims.of_int (20)) (Prims.of_int (2))
                          (Prims.of_int (27)) (Prims.of_int (48)))))
                 (Obj.magic uu___1)
                 (fun uu___2 ->
                    (fun se ->
                       match se with
                       | FStar_Pervasives_Native.None ->
                           Obj.magic
                             (Obj.repr
                                (FStar_Tactics_V2_Derived.fail
                                   "ctors_of_typ: type not found"))
                       | FStar_Pervasives_Native.Some se1 ->
                           Obj.magic
                             (Obj.repr
                                (let uu___2 =
                                   FStar_Tactics_NamedView.inspect_sigelt se1 in
                                 FStar_Tactics_Effect.tac_bind
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "FStar.Tactics.TypeRepr.fst"
                                            (Prims.of_int (23))
                                            (Prims.of_int (14))
                                            (Prims.of_int (23))
                                            (Prims.of_int (31)))))
                                   (FStar_Sealed.seal
                                      (Obj.magic
                                         (FStar_Range.mk_range
                                            "FStar.Tactics.TypeRepr.fst"
                                            (Prims.of_int (24))
                                            (Prims.of_int (4))
                                            (Prims.of_int (27))
                                            (Prims.of_int (48)))))
                                   (Obj.magic uu___2)
                                   (fun sev ->
                                      if
                                        FStar_Tactics_NamedView.uu___is_Sg_Inductive
                                          sev
                                      then
                                        FStar_Tactics_Effect.lift_div_tac
                                          (fun uu___3 -> sev)
                                      else
                                        FStar_Tactics_V2_Derived.fail
                                          "ctors_of_typ: not an inductive type"))))
                      uu___2))) uu___1)
let (alg_ctor :
  FStarC_Reflection_Types.typ ->
    (FStarC_Reflection_Types.typ, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun ty ->
    let uu___ = FStar_Tactics_V2_SyntaxHelpers.collect_arr ty in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.TypeRepr.fst"
               (Prims.of_int (30)) (Prims.of_int (15)) (Prims.of_int (30))
               (Prims.of_int (29)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.TypeRepr.fst"
               (Prims.of_int (29)) (Prims.of_int (35)) (Prims.of_int (31))
               (Prims.of_int (67))))) (Obj.magic uu___)
      (fun uu___1 ->
         (fun uu___1 ->
            match uu___1 with
            | (tys, c) ->
                Obj.magic
                  (FStar_Tactics_Util.fold_right
                     (fun uu___3 ->
                        fun uu___2 ->
                          (fun ty1 ->
                             fun acc ->
                               Obj.magic
                                 (FStar_Tactics_Effect.lift_div_tac
                                    (fun uu___2 -> tuple2_ ty1 acc))) uu___3
                            uu___2) tys unitt_)) uu___1)
let (generate_repr_typ :
  FStar_Tactics_NamedView.binders ->
    FStarC_Reflection_V2_Data.ctor Prims.list ->
      (FStarC_Reflection_Types.typ, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun params ->
    fun ctors ->
      let uu___ =
        FStar_Tactics_Util.map
          (fun uu___1 -> match uu___1 with | (uu___2, ty) -> alg_ctor ty)
          ctors in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.TypeRepr.fst"
                 (Prims.of_int (35)) (Prims.of_int (18)) (Prims.of_int (35))
                 (Prims.of_int (61)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.TypeRepr.fst"
                 (Prims.of_int (35)) (Prims.of_int (64)) (Prims.of_int (38))
                 (Prims.of_int (17))))) (Obj.magic uu___)
        (fun uu___1 ->
           (fun ctor_typs ->
              let uu___1 =
                FStar_Tactics_Util.fold_right
                  (fun uu___3 ->
                     fun uu___2 ->
                       (fun ty ->
                          fun acc ->
                            Obj.magic
                              (FStar_Tactics_Effect.lift_div_tac
                                 (fun uu___2 -> either_ ty acc))) uu___3
                         uu___2) ctor_typs empty_ in
              Obj.magic
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "FStar.Tactics.TypeRepr.fst"
                            (Prims.of_int (37)) (Prims.of_int (4))
                            (Prims.of_int (37)) (Prims.of_int (67)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range "FStar.Tactics.TypeRepr.fst"
                            (Prims.of_int (36)) (Prims.of_int (6))
                            (Prims.of_int (36)) (Prims.of_int (21)))))
                   (Obj.magic uu___1)
                   (fun alternative_typ ->
                      FStar_Tactics_Effect.lift_div_tac
                        (fun uu___2 -> alternative_typ)))) uu___1)
let _ =
  FStarC_Tactics_Native.register_tactic
    "FStar.Tactics.TypeRepr.generate_repr_typ" (Prims.of_int (3))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             FStarC_Tactics_InterpFuns.mk_tactic_interpretation_2
               "FStar.Tactics.TypeRepr.generate_repr_typ (plugin)"
               (FStarC_Tactics_Native.from_tactic_2 generate_repr_typ)
               (FStarC_Syntax_Embeddings.e_list
                  FStar_Tactics_NamedView.e_binder)
               (FStarC_Syntax_Embeddings.e_list
                  (FStarC_Syntax_Embeddings.e_tuple2
                     (FStarC_Syntax_Embeddings.e_list
                        FStarC_Syntax_Embeddings.e_string)
                     FStarC_Reflection_V2_Embeddings.e_term))
               FStarC_Reflection_V2_Embeddings.e_term psc ncb us args)
let (generate_down : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    let uu___1 = FStarC_Tactics_V2_Builtins.intro () in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.TypeRepr.fst"
               (Prims.of_int (43)) (Prims.of_int (10)) (Prims.of_int (43))
               (Prims.of_int (18)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.TypeRepr.fst"
               (Prims.of_int (43)) (Prims.of_int (21)) (Prims.of_int (52))
               (Prims.of_int (3))))) (Obj.magic uu___1)
      (fun uu___2 ->
         (fun b ->
            let uu___2 =
              FStarC_Tactics_V2_Builtins.t_destruct
                (FStar_Tactics_V2_SyntaxCoercions.binding_to_term b) in
            Obj.magic
              (FStar_Tactics_Effect.tac_bind
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "FStar.Tactics.TypeRepr.fst"
                          (Prims.of_int (44)) (Prims.of_int (14))
                          (Prims.of_int (44)) (Prims.of_int (26)))))
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "FStar.Tactics.TypeRepr.fst"
                          (Prims.of_int (45)) (Prims.of_int (2))
                          (Prims.of_int (52)) (Prims.of_int (3)))))
                 (Obj.magic uu___2)
                 (fun uu___3 ->
                    (fun cases ->
                       Obj.magic
                         (FStar_Tactics_Util.iteri
                            (fun i ->
                               fun uu___3 ->
                                 match uu___3 with
                                 | (c, n) ->
                                     let uu___4 =
                                       FStar_Tactics_Util.repeatn n
                                         (fun uu___5 ->
                                            FStarC_Tactics_V2_Builtins.intro
                                              ()) in
                                     FStar_Tactics_Effect.tac_bind
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "FStar.Tactics.TypeRepr.fst"
                                                (Prims.of_int (46))
                                                (Prims.of_int (13))
                                                (Prims.of_int (46))
                                                (Prims.of_int (42)))))
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "FStar.Tactics.TypeRepr.fst"
                                                (Prims.of_int (46))
                                                (Prims.of_int (45))
                                                (Prims.of_int (51))
                                                (Prims.of_int (13)))))
                                       (Obj.magic uu___4)
                                       (fun uu___5 ->
                                          (fun bs ->
                                             let uu___5 =
                                               FStarC_Tactics_V2_Builtins.intro
                                                 () in
                                             Obj.magic
                                               (FStar_Tactics_Effect.tac_bind
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "FStar.Tactics.TypeRepr.fst"
                                                           (Prims.of_int (47))
                                                           (Prims.of_int (16))
                                                           (Prims.of_int (47))
                                                           (Prims.of_int (24)))))
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "FStar.Tactics.TypeRepr.fst"
                                                           (Prims.of_int (47))
                                                           (Prims.of_int (27))
                                                           (Prims.of_int (51))
                                                           (Prims.of_int (13)))))
                                                  (Obj.magic uu___5)
                                                  (fun uu___6 ->
                                                     (fun _b_eq ->
                                                        let uu___6 =
                                                          FStar_Tactics_Util.fold_right
                                                            (fun uu___8 ->
                                                               fun uu___7 ->
                                                                 (fun b1 ->
                                                                    fun acc
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___7 ->
                                                                    mktuple2_
                                                                    (FStar_Tactics_V2_SyntaxCoercions.binding_to_term
                                                                    b1) acc)))
                                                                   uu___8
                                                                   uu___7) bs
                                                            unitv_ in
                                                        Obj.magic
                                                          (FStar_Tactics_Effect.tac_bind
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "FStar.Tactics.TypeRepr.fst"
                                                                    (Prims.of_int (48))
                                                                    (Prims.of_int (14))
                                                                    (Prims.of_int (48))
                                                                    (Prims.of_int (80)))))
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "FStar.Tactics.TypeRepr.fst"
                                                                    (Prims.of_int (48))
                                                                    (Prims.of_int (83))
                                                                    (Prims.of_int (51))
                                                                    (Prims.of_int (13)))))
                                                             (Obj.magic
                                                                uu___6)
                                                             (fun uu___7 ->
                                                                (fun sol ->
                                                                   let uu___7
                                                                    =
                                                                    FStar_Tactics_Util.repeatn
                                                                    i
                                                                    (fun
                                                                    uu___8 ->
                                                                    FStar_Tactics_V2_Derived.apply
                                                                    (FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_FVar
                                                                    (FStarC_Reflection_V2_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Pervasives";
                                                                    "Inr"])))) in
                                                                   Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.TypeRepr.fst"
                                                                    (Prims.of_int (49))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (49))
                                                                    (Prims.of_int (45)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.TypeRepr.fst"
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (51))
                                                                    (Prims.of_int (13)))))
                                                                    (Obj.magic
                                                                    uu___7)
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun
                                                                    uu___8 ->
                                                                    let uu___9
                                                                    =
                                                                    FStar_Tactics_V2_Derived.apply
                                                                    (FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_FVar
                                                                    (FStarC_Reflection_V2_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Pervasives";
                                                                    "Inl"]))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.TypeRepr.fst"
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (50))
                                                                    (Prims.of_int (16)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.TypeRepr.fst"
                                                                    (Prims.of_int (51))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (51))
                                                                    (Prims.of_int (13)))))
                                                                    (Obj.magic
                                                                    uu___9)
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_V2_Derived.exact
                                                                    sol))
                                                                    uu___10)))
                                                                    uu___8)))
                                                                  uu___7)))
                                                       uu___6))) uu___5))
                            cases)) uu___3))) uu___2)
let _ =
  FStarC_Tactics_Native.register_tactic
    "FStar.Tactics.TypeRepr.generate_down" (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.TypeRepr.generate_down (plugin)"
               (FStarC_Tactics_Native.from_tactic_1 generate_down)
               FStarC_Syntax_Embeddings.e_unit
               FStarC_Syntax_Embeddings.e_unit psc ncb us args)
let rec (get_apply_tuple :
  FStar_Tactics_NamedView.binding ->
    (FStar_Tactics_NamedView.binding Prims.list, unit)
      FStar_Tactics_Effect.tac_repr)
  =
  fun b ->
    let uu___ =
      FStar_Tactics_V2_SyntaxHelpers.collect_app
        b.FStarC_Reflection_V2_Data.sort3 in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.TypeRepr.fst"
               (Prims.of_int (55)) (Prims.of_int (17)) (Prims.of_int (55))
               (Prims.of_int (35)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.TypeRepr.fst"
               (Prims.of_int (54)) (Prims.of_int (58)) (Prims.of_int (74))
               (Prims.of_int (69))))) (Obj.magic uu___)
      (fun uu___1 ->
         (fun uu___1 ->
            match uu___1 with
            | (hd, args) ->
                let uu___2 =
                  let uu___3 = FStar_Tactics_NamedView.inspect hd in
                  FStar_Tactics_Effect.tac_bind
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range "FStar.Tactics.TypeRepr.fst"
                             (Prims.of_int (56)) (Prims.of_int (8))
                             (Prims.of_int (56)) (Prims.of_int (18)))))
                    (FStar_Sealed.seal
                       (Obj.magic
                          (FStar_Range.mk_range "FStar.Tactics.TypeRepr.fst"
                             (Prims.of_int (56)) (Prims.of_int (8))
                             (Prims.of_int (56)) (Prims.of_int (24)))))
                    (Obj.magic uu___3)
                    (fun uu___4 ->
                       FStar_Tactics_Effect.lift_div_tac
                         (fun uu___5 -> (uu___4, args))) in
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "FStar.Tactics.TypeRepr.fst"
                              (Prims.of_int (56)) (Prims.of_int (8))
                              (Prims.of_int (56)) (Prims.of_int (24)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "FStar.Tactics.TypeRepr.fst"
                              (Prims.of_int (56)) (Prims.of_int (2))
                              (Prims.of_int (74)) (Prims.of_int (69)))))
                     (Obj.magic uu___2)
                     (fun uu___3 ->
                        (fun uu___3 ->
                           match uu___3 with
                           | (FStar_Tactics_NamedView.Tv_UInst (fv, uu___4),
                              b1::b2::[]) ->
                               Obj.magic
                                 (Obj.repr
                                    (if
                                       (FStarC_Reflection_V2_Builtins.inspect_fv
                                          fv)
                                         =
                                         ["FStar";
                                         "Pervasives";
                                         "Native";
                                         "tuple2"]
                                     then
                                       let uu___5 =
                                         FStarC_Tactics_V2_Builtins.t_destruct
                                           (FStar_Tactics_V2_SyntaxCoercions.binding_to_term
                                              b) in
                                       FStar_Tactics_Effect.tac_bind
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "FStar.Tactics.TypeRepr.fst"
                                                  (Prims.of_int (60))
                                                  (Prims.of_int (18))
                                                  (Prims.of_int (60))
                                                  (Prims.of_int (30)))))
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "FStar.Tactics.TypeRepr.fst"
                                                  (Prims.of_int (61))
                                                  (Prims.of_int (6))
                                                  (Prims.of_int (65))
                                                  (Prims.of_int (30)))))
                                         (Obj.magic uu___5)
                                         (fun uu___6 ->
                                            (fun cases ->
                                               let uu___6 =
                                                 FStar_Tactics_V2_Derived.guard
                                                   ((((FStar_List_Tot_Base.length
                                                         cases)
                                                        = Prims.int_one)
                                                       &&
                                                       ((FStarC_Reflection_V2_Builtins.inspect_fv
                                                           (FStar_Pervasives_Native.fst
                                                              (FStar_List_Tot_Base.hd
                                                                 cases)))
                                                          =
                                                          ["FStar";
                                                          "Pervasives";
                                                          "Native";
                                                          "Mktuple2"]))
                                                      &&
                                                      ((FStar_Pervasives_Native.snd
                                                          (FStar_List_Tot_Base.hd
                                                             cases))
                                                         = (Prims.of_int (2)))) in
                                               Obj.magic
                                                 (FStar_Tactics_Effect.tac_bind
                                                    (FStar_Sealed.seal
                                                       (Obj.magic
                                                          (FStar_Range.mk_range
                                                             "FStar.Tactics.TypeRepr.fst"
                                                             (Prims.of_int (61))
                                                             (Prims.of_int (6))
                                                             (Prims.of_int (61))
                                                             (Prims.of_int (136)))))
                                                    (FStar_Sealed.seal
                                                       (Obj.magic
                                                          (FStar_Range.mk_range
                                                             "FStar.Tactics.TypeRepr.fst"
                                                             (Prims.of_int (61))
                                                             (Prims.of_int (137))
                                                             (Prims.of_int (65))
                                                             (Prims.of_int (30)))))
                                                    (Obj.magic uu___6)
                                                    (fun uu___7 ->
                                                       (fun uu___7 ->
                                                          let uu___8 =
                                                            FStarC_Tactics_V2_Builtins.intro
                                                              () in
                                                          Obj.magic
                                                            (FStar_Tactics_Effect.tac_bind
                                                               (FStar_Sealed.seal
                                                                  (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.TypeRepr.fst"
                                                                    (Prims.of_int (62))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (62))
                                                                    (Prims.of_int (23)))))
                                                               (FStar_Sealed.seal
                                                                  (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.TypeRepr.fst"
                                                                    (Prims.of_int (62))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (65))
                                                                    (Prims.of_int (30)))))
                                                               (Obj.magic
                                                                  uu___8)
                                                               (fun uu___9 ->
                                                                  (fun b11 ->
                                                                    let uu___9
                                                                    =
                                                                    FStarC_Tactics_V2_Builtins.intro
                                                                    () in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.TypeRepr.fst"
                                                                    (Prims.of_int (63))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (63))
                                                                    (Prims.of_int (23)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.TypeRepr.fst"
                                                                    (Prims.of_int (63))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (65))
                                                                    (Prims.of_int (30)))))
                                                                    (Obj.magic
                                                                    uu___9)
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun b21
                                                                    ->
                                                                    let uu___10
                                                                    =
                                                                    FStarC_Tactics_V2_Builtins.intro
                                                                    () in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.TypeRepr.fst"
                                                                    (Prims.of_int (64))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (64))
                                                                    (Prims.of_int (24)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.TypeRepr.fst"
                                                                    (Prims.of_int (65))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (65))
                                                                    (Prims.of_int (30)))))
                                                                    (Obj.magic
                                                                    uu___10)
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    (fun _eq
                                                                    ->
                                                                    let uu___11
                                                                    =
                                                                    get_apply_tuple
                                                                    b21 in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.TypeRepr.fst"
                                                                    (Prims.of_int (65))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (65))
                                                                    (Prims.of_int (30)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.TypeRepr.fst"
                                                                    (Prims.of_int (65))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (65))
                                                                    (Prims.of_int (30)))))
                                                                    (Obj.magic
                                                                    uu___11)
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___13
                                                                    -> b11 ::
                                                                    uu___12))))
                                                                    uu___11)))
                                                                    uu___10)))
                                                                    uu___9)))
                                                         uu___7))) uu___6)
                                     else
                                       (let uu___6 =
                                          let uu___7 =
                                            FStarC_Tactics_V2_Builtins.term_to_string
                                              b.FStarC_Reflection_V2_Data.sort3 in
                                          FStar_Tactics_Effect.tac_bind
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "FStar.Tactics.TypeRepr.fst"
                                                     (Prims.of_int (67))
                                                     (Prims.of_int (49))
                                                     (Prims.of_int (67))
                                                     (Prims.of_int (70)))))
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
                                                      "unexpected term in apply_tuple: "
                                                      uu___8)) in
                                        FStar_Tactics_Effect.tac_bind
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "FStar.Tactics.TypeRepr.fst"
                                                   (Prims.of_int (67))
                                                   (Prims.of_int (11))
                                                   (Prims.of_int (67))
                                                   (Prims.of_int (71)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "FStar.Tactics.TypeRepr.fst"
                                                   (Prims.of_int (67))
                                                   (Prims.of_int (6))
                                                   (Prims.of_int (67))
                                                   (Prims.of_int (71)))))
                                          (Obj.magic uu___6)
                                          (fun uu___7 ->
                                             FStar_Tactics_V2_Derived.fail
                                               uu___7))))
                           | (FStar_Tactics_NamedView.Tv_FVar fv, b1::b2::[])
                               ->
                               Obj.magic
                                 (Obj.repr
                                    (if
                                       (FStarC_Reflection_V2_Builtins.inspect_fv
                                          fv)
                                         =
                                         ["FStar";
                                         "Pervasives";
                                         "Native";
                                         "tuple2"]
                                     then
                                       let uu___4 =
                                         FStarC_Tactics_V2_Builtins.t_destruct
                                           (FStar_Tactics_V2_SyntaxCoercions.binding_to_term
                                              b) in
                                       FStar_Tactics_Effect.tac_bind
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "FStar.Tactics.TypeRepr.fst"
                                                  (Prims.of_int (60))
                                                  (Prims.of_int (18))
                                                  (Prims.of_int (60))
                                                  (Prims.of_int (30)))))
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "FStar.Tactics.TypeRepr.fst"
                                                  (Prims.of_int (61))
                                                  (Prims.of_int (6))
                                                  (Prims.of_int (65))
                                                  (Prims.of_int (30)))))
                                         (Obj.magic uu___4)
                                         (fun uu___5 ->
                                            (fun cases ->
                                               let uu___5 =
                                                 FStar_Tactics_V2_Derived.guard
                                                   ((((FStar_List_Tot_Base.length
                                                         cases)
                                                        = Prims.int_one)
                                                       &&
                                                       ((FStarC_Reflection_V2_Builtins.inspect_fv
                                                           (FStar_Pervasives_Native.fst
                                                              (FStar_List_Tot_Base.hd
                                                                 cases)))
                                                          =
                                                          ["FStar";
                                                          "Pervasives";
                                                          "Native";
                                                          "Mktuple2"]))
                                                      &&
                                                      ((FStar_Pervasives_Native.snd
                                                          (FStar_List_Tot_Base.hd
                                                             cases))
                                                         = (Prims.of_int (2)))) in
                                               Obj.magic
                                                 (FStar_Tactics_Effect.tac_bind
                                                    (FStar_Sealed.seal
                                                       (Obj.magic
                                                          (FStar_Range.mk_range
                                                             "FStar.Tactics.TypeRepr.fst"
                                                             (Prims.of_int (61))
                                                             (Prims.of_int (6))
                                                             (Prims.of_int (61))
                                                             (Prims.of_int (136)))))
                                                    (FStar_Sealed.seal
                                                       (Obj.magic
                                                          (FStar_Range.mk_range
                                                             "FStar.Tactics.TypeRepr.fst"
                                                             (Prims.of_int (61))
                                                             (Prims.of_int (137))
                                                             (Prims.of_int (65))
                                                             (Prims.of_int (30)))))
                                                    (Obj.magic uu___5)
                                                    (fun uu___6 ->
                                                       (fun uu___6 ->
                                                          let uu___7 =
                                                            FStarC_Tactics_V2_Builtins.intro
                                                              () in
                                                          Obj.magic
                                                            (FStar_Tactics_Effect.tac_bind
                                                               (FStar_Sealed.seal
                                                                  (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.TypeRepr.fst"
                                                                    (Prims.of_int (62))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (62))
                                                                    (Prims.of_int (23)))))
                                                               (FStar_Sealed.seal
                                                                  (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.TypeRepr.fst"
                                                                    (Prims.of_int (62))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (65))
                                                                    (Prims.of_int (30)))))
                                                               (Obj.magic
                                                                  uu___7)
                                                               (fun uu___8 ->
                                                                  (fun b11 ->
                                                                    let uu___8
                                                                    =
                                                                    FStarC_Tactics_V2_Builtins.intro
                                                                    () in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.TypeRepr.fst"
                                                                    (Prims.of_int (63))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (63))
                                                                    (Prims.of_int (23)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.TypeRepr.fst"
                                                                    (Prims.of_int (63))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (65))
                                                                    (Prims.of_int (30)))))
                                                                    (Obj.magic
                                                                    uu___8)
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun b21
                                                                    ->
                                                                    let uu___9
                                                                    =
                                                                    FStarC_Tactics_V2_Builtins.intro
                                                                    () in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.TypeRepr.fst"
                                                                    (Prims.of_int (64))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (64))
                                                                    (Prims.of_int (24)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.TypeRepr.fst"
                                                                    (Prims.of_int (65))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (65))
                                                                    (Prims.of_int (30)))))
                                                                    (Obj.magic
                                                                    uu___9)
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun _eq
                                                                    ->
                                                                    let uu___10
                                                                    =
                                                                    get_apply_tuple
                                                                    b21 in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.TypeRepr.fst"
                                                                    (Prims.of_int (65))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (65))
                                                                    (Prims.of_int (30)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.TypeRepr.fst"
                                                                    (Prims.of_int (65))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (65))
                                                                    (Prims.of_int (30)))))
                                                                    (Obj.magic
                                                                    uu___10)
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___12
                                                                    -> b11 ::
                                                                    uu___11))))
                                                                    uu___10)))
                                                                    uu___9)))
                                                                    uu___8)))
                                                         uu___6))) uu___5)
                                     else
                                       (let uu___5 =
                                          let uu___6 =
                                            FStarC_Tactics_V2_Builtins.term_to_string
                                              b.FStarC_Reflection_V2_Data.sort3 in
                                          FStar_Tactics_Effect.tac_bind
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "FStar.Tactics.TypeRepr.fst"
                                                     (Prims.of_int (67))
                                                     (Prims.of_int (49))
                                                     (Prims.of_int (67))
                                                     (Prims.of_int (70)))))
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
                                                      "unexpected term in apply_tuple: "
                                                      uu___7)) in
                                        FStar_Tactics_Effect.tac_bind
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "FStar.Tactics.TypeRepr.fst"
                                                   (Prims.of_int (67))
                                                   (Prims.of_int (11))
                                                   (Prims.of_int (67))
                                                   (Prims.of_int (71)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "FStar.Tactics.TypeRepr.fst"
                                                   (Prims.of_int (67))
                                                   (Prims.of_int (6))
                                                   (Prims.of_int (67))
                                                   (Prims.of_int (71)))))
                                          (Obj.magic uu___5)
                                          (fun uu___6 ->
                                             FStar_Tactics_V2_Derived.fail
                                               uu___6))))
                           | (FStar_Tactics_NamedView.Tv_FVar fv, []) ->
                               Obj.magic
                                 (Obj.repr
                                    (if
                                       (FStarC_Reflection_V2_Builtins.inspect_fv
                                          fv)
                                         = ["Prims"; "unit"]
                                     then
                                       Obj.repr
                                         (FStar_Tactics_Effect.lift_div_tac
                                            (fun uu___4 -> []))
                                     else
                                       Obj.repr
                                         (let uu___5 =
                                            let uu___6 =
                                              FStarC_Tactics_V2_Builtins.term_to_string
                                                b.FStarC_Reflection_V2_Data.sort3 in
                                            FStar_Tactics_Effect.tac_bind
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "FStar.Tactics.TypeRepr.fst"
                                                       (Prims.of_int (72))
                                                       (Prims.of_int (49))
                                                       (Prims.of_int (72))
                                                       (Prims.of_int (70)))))
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
                                                        "unexpected term in apply_tuple: "
                                                        uu___7)) in
                                          FStar_Tactics_Effect.tac_bind
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "FStar.Tactics.TypeRepr.fst"
                                                     (Prims.of_int (72))
                                                     (Prims.of_int (11))
                                                     (Prims.of_int (72))
                                                     (Prims.of_int (71)))))
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "FStar.Tactics.TypeRepr.fst"
                                                     (Prims.of_int (72))
                                                     (Prims.of_int (6))
                                                     (Prims.of_int (72))
                                                     (Prims.of_int (71)))))
                                            (Obj.magic uu___5)
                                            (fun uu___6 ->
                                               FStar_Tactics_V2_Derived.fail
                                                 uu___6))))
                           | uu___4 ->
                               Obj.magic
                                 (Obj.repr
                                    (let uu___5 =
                                       let uu___6 =
                                         FStarC_Tactics_V2_Builtins.term_to_string
                                           b.FStarC_Reflection_V2_Data.sort3 in
                                       FStar_Tactics_Effect.tac_bind
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "FStar.Tactics.TypeRepr.fst"
                                                  (Prims.of_int (74))
                                                  (Prims.of_int (47))
                                                  (Prims.of_int (74))
                                                  (Prims.of_int (68)))))
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
                                                   "unexpected term in apply_tuple: "
                                                   uu___7)) in
                                     FStar_Tactics_Effect.tac_bind
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "FStar.Tactics.TypeRepr.fst"
                                                (Prims.of_int (74))
                                                (Prims.of_int (9))
                                                (Prims.of_int (74))
                                                (Prims.of_int (69)))))
                                       (FStar_Sealed.seal
                                          (Obj.magic
                                             (FStar_Range.mk_range
                                                "FStar.Tactics.TypeRepr.fst"
                                                (Prims.of_int (74))
                                                (Prims.of_int (4))
                                                (Prims.of_int (74))
                                                (Prims.of_int (69)))))
                                       (Obj.magic uu___5)
                                       (fun uu___6 ->
                                          FStar_Tactics_V2_Derived.fail
                                            uu___6)))) uu___3))) uu___1)
let rec (generate_up_aux :
  FStarC_Reflection_V2_Data.ctor Prims.list ->
    FStar_Tactics_NamedView.binding ->
      (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun ctors ->
    fun b ->
      match ctors with
      | [] ->
          let uu___ =
            FStar_Tactics_V2_Derived.apply
              (FStarC_Reflection_V2_Builtins.pack_ln
                 (FStarC_Reflection_V2_Data.Tv_FVar
                    (FStarC_Reflection_V2_Builtins.pack_fv
                       ["FStar"; "Tactics"; "TypeRepr"; "empty_elim"]))) in
          FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "FStar.Tactics.TypeRepr.fst"
                     (Prims.of_int (82)) (Prims.of_int (4))
                     (Prims.of_int (82)) (Prims.of_int (23)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "FStar.Tactics.TypeRepr.fst"
                     (Prims.of_int (83)) (Prims.of_int (4))
                     (Prims.of_int (83)) (Prims.of_int (11)))))
            (Obj.magic uu___)
            (fun uu___1 ->
               (fun uu___1 ->
                  Obj.magic
                    (FStar_Tactics_V2_Derived.exact
                       (FStar_Tactics_V2_SyntaxCoercions.binding_to_term b)))
                 uu___1)
      | c::cs ->
          let uu___ =
            FStarC_Tactics_V2_Builtins.t_destruct
              (FStar_Tactics_V2_SyntaxCoercions.binding_to_term b) in
          FStar_Tactics_Effect.tac_bind
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "FStar.Tactics.TypeRepr.fst"
                     (Prims.of_int (85)) (Prims.of_int (16))
                     (Prims.of_int (85)) (Prims.of_int (28)))))
            (FStar_Sealed.seal
               (Obj.magic
                  (FStar_Range.mk_range "FStar.Tactics.TypeRepr.fst"
                     (Prims.of_int (86)) (Prims.of_int (4))
                     (Prims.of_int (99)) (Prims.of_int (24)))))
            (Obj.magic uu___)
            (fun uu___1 ->
               (fun cases ->
                  let uu___1 =
                    if
                      (FStar_List_Tot_Base.length cases) <>
                        (Prims.of_int (2))
                    then
                      Obj.magic
                        (FStar_Tactics_V2_Derived.fail
                           "generate_up_aux: expected Inl/Inr???")
                    else
                      Obj.magic
                        (FStar_Tactics_Effect.lift_div_tac (fun uu___3 -> ())) in
                  Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "FStar.Tactics.TypeRepr.fst"
                                (Prims.of_int (86)) (Prims.of_int (4))
                                (Prims.of_int (87)) (Prims.of_int (49)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "FStar.Tactics.TypeRepr.fst"
                                (Prims.of_int (88)) (Prims.of_int (4))
                                (Prims.of_int (99)) (Prims.of_int (24)))))
                       (Obj.magic uu___1)
                       (fun uu___2 ->
                          (fun uu___2 ->
                             let uu___3 =
                               FStar_Tactics_V2_Derived.focus
                                 (fun uu___4 ->
                                    let uu___5 =
                                      FStarC_Tactics_V2_Builtins.intro () in
                                    FStar_Tactics_Effect.tac_bind
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "FStar.Tactics.TypeRepr.fst"
                                               (Prims.of_int (89))
                                               (Prims.of_int (15))
                                               (Prims.of_int (89))
                                               (Prims.of_int (23)))))
                                      (FStar_Sealed.seal
                                         (Obj.magic
                                            (FStar_Range.mk_range
                                               "FStar.Tactics.TypeRepr.fst"
                                               (Prims.of_int (89))
                                               (Prims.of_int (26))
                                               (Prims.of_int (95))
                                               (Prims.of_int (11)))))
                                      (Obj.magic uu___5)
                                      (fun uu___6 ->
                                         (fun b' ->
                                            let uu___6 =
                                              FStarC_Tactics_V2_Builtins.intro
                                                () in
                                            Obj.magic
                                              (FStar_Tactics_Effect.tac_bind
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "FStar.Tactics.TypeRepr.fst"
                                                          (Prims.of_int (90))
                                                          (Prims.of_int (16))
                                                          (Prims.of_int (90))
                                                          (Prims.of_int (24)))))
                                                 (FStar_Sealed.seal
                                                    (Obj.magic
                                                       (FStar_Range.mk_range
                                                          "FStar.Tactics.TypeRepr.fst"
                                                          (Prims.of_int (90))
                                                          (Prims.of_int (27))
                                                          (Prims.of_int (95))
                                                          (Prims.of_int (11)))))
                                                 (Obj.magic uu___6)
                                                 (fun uu___7 ->
                                                    (fun _eq ->
                                                       let uu___7 =
                                                         Obj.magic
                                                           (FStar_Tactics_Effect.lift_div_tac
                                                              (fun uu___8 ->
                                                                 FStar_Pervasives_Native.fst
                                                                   c)) in
                                                       Obj.magic
                                                         (FStar_Tactics_Effect.tac_bind
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "FStar.Tactics.TypeRepr.fst"
                                                                    (Prims.of_int (91))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (91))
                                                                    (Prims.of_int (24)))))
                                                            (FStar_Sealed.seal
                                                               (Obj.magic
                                                                  (FStar_Range.mk_range
                                                                    "FStar.Tactics.TypeRepr.fst"
                                                                    (Prims.of_int (91))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (95))
                                                                    (Prims.of_int (11)))))
                                                            (Obj.magic uu___7)
                                                            (fun uu___8 ->
                                                               (fun c_name ->
                                                                  let uu___8
                                                                    =
                                                                    get_apply_tuple
                                                                    b' in
                                                                  Obj.magic
                                                                    (
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.TypeRepr.fst"
                                                                    (Prims.of_int (92))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (92))
                                                                    (Prims.of_int (35)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.TypeRepr.fst"
                                                                    (Prims.of_int (93))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (95))
                                                                    (Prims.of_int (11)))))
                                                                    (Obj.magic
                                                                    uu___8)
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun args
                                                                    ->
                                                                    let uu___9
                                                                    =
                                                                    FStar_Tactics_V2_Derived.apply
                                                                    (FStar_Tactics_NamedView.pack
                                                                    (FStar_Tactics_NamedView.Tv_FVar
                                                                    (FStarC_Reflection_V2_Builtins.pack_fv
                                                                    c_name))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.TypeRepr.fst"
                                                                    (Prims.of_int (93))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (93))
                                                                    (Prims.of_int (45)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.TypeRepr.fst"
                                                                    (Prims.of_int (94))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (95))
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
                                                                    FStar_Tactics_Util.iter
                                                                    (fun b1
                                                                    ->
                                                                    FStar_Tactics_V2_Derived.exact
                                                                    (FStar_Tactics_V2_SyntaxCoercions.binding_to_term
                                                                    b1)) args in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.TypeRepr.fst"
                                                                    (Prims.of_int (94))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (94))
                                                                    (Prims.of_int (49)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.TypeRepr.fst"
                                                                    (Prims.of_int (95))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (95))
                                                                    (Prims.of_int (11)))))
                                                                    (Obj.magic
                                                                    uu___11)
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_V2_Derived.qed
                                                                    ()))
                                                                    uu___12)))
                                                                    uu___10)))
                                                                    uu___9)))
                                                                 uu___8)))
                                                      uu___7))) uu___6)) in
                             Obj.magic
                               (FStar_Tactics_Effect.tac_bind
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "FStar.Tactics.TypeRepr.fst"
                                           (Prims.of_int (88))
                                           (Prims.of_int (4))
                                           (Prims.of_int (96))
                                           (Prims.of_int (5)))))
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "FStar.Tactics.TypeRepr.fst"
                                           (Prims.of_int (96))
                                           (Prims.of_int (6))
                                           (Prims.of_int (99))
                                           (Prims.of_int (24)))))
                                  (Obj.magic uu___3)
                                  (fun uu___4 ->
                                     (fun uu___4 ->
                                        let uu___5 =
                                          FStarC_Tactics_V2_Builtins.intro () in
                                        Obj.magic
                                          (FStar_Tactics_Effect.tac_bind
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "FStar.Tactics.TypeRepr.fst"
                                                      (Prims.of_int (97))
                                                      (Prims.of_int (12))
                                                      (Prims.of_int (97))
                                                      (Prims.of_int (20)))))
                                             (FStar_Sealed.seal
                                                (Obj.magic
                                                   (FStar_Range.mk_range
                                                      "FStar.Tactics.TypeRepr.fst"
                                                      (Prims.of_int (97))
                                                      (Prims.of_int (23))
                                                      (Prims.of_int (99))
                                                      (Prims.of_int (24)))))
                                             (Obj.magic uu___5)
                                             (fun uu___6 ->
                                                (fun b1 ->
                                                   let uu___6 =
                                                     FStarC_Tactics_V2_Builtins.intro
                                                       () in
                                                   Obj.magic
                                                     (FStar_Tactics_Effect.tac_bind
                                                        (FStar_Sealed.seal
                                                           (Obj.magic
                                                              (FStar_Range.mk_range
                                                                 "FStar.Tactics.TypeRepr.fst"
                                                                 (Prims.of_int (98))
                                                                 (Prims.of_int (14))
                                                                 (Prims.of_int (98))
                                                                 (Prims.of_int (22)))))
                                                        (FStar_Sealed.seal
                                                           (Obj.magic
                                                              (FStar_Range.mk_range
                                                                 "FStar.Tactics.TypeRepr.fst"
                                                                 (Prims.of_int (99))
                                                                 (Prims.of_int (4))
                                                                 (Prims.of_int (99))
                                                                 (Prims.of_int (24)))))
                                                        (Obj.magic uu___6)
                                                        (fun uu___7 ->
                                                           (fun _eq ->
                                                              Obj.magic
                                                                (generate_up_aux
                                                                   cs b1))
                                                             uu___7))) uu___6)))
                                       uu___4))) uu___2))) uu___1)
let (generate_up :
  Prims.string -> unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun nm ->
    fun uu___ ->
      let uu___1 = get_inductive_typ nm in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.TypeRepr.fst"
                 (Prims.of_int (104)) (Prims.of_int (29))
                 (Prims.of_int (104)) (Prims.of_int (49)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.TypeRepr.fst"
                 (Prims.of_int (103)) (Prims.of_int (43))
                 (Prims.of_int (106)) (Prims.of_int (25)))))
        (Obj.magic uu___1)
        (fun uu___2 ->
           (fun uu___2 ->
              match uu___2 with
              | FStar_Tactics_NamedView.Sg_Inductive
                  { FStar_Tactics_NamedView.nm = uu___3;
                    FStar_Tactics_NamedView.univs1 = uu___4;
                    FStar_Tactics_NamedView.params = uu___5;
                    FStar_Tactics_NamedView.typ = uu___6;
                    FStar_Tactics_NamedView.ctors = ctors;_}
                  ->
                  let uu___7 = FStarC_Tactics_V2_Builtins.intro () in
                  Obj.magic
                    (FStar_Tactics_Effect.tac_bind
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "FStar.Tactics.TypeRepr.fst"
                                (Prims.of_int (105)) (Prims.of_int (10))
                                (Prims.of_int (105)) (Prims.of_int (18)))))
                       (FStar_Sealed.seal
                          (Obj.magic
                             (FStar_Range.mk_range
                                "FStar.Tactics.TypeRepr.fst"
                                (Prims.of_int (106)) (Prims.of_int (2))
                                (Prims.of_int (106)) (Prims.of_int (25)))))
                       (Obj.magic uu___7)
                       (fun uu___8 ->
                          (fun b -> Obj.magic (generate_up_aux ctors b))
                            uu___8))) uu___2)
let _ =
  FStarC_Tactics_Native.register_tactic "FStar.Tactics.TypeRepr.generate_up"
    (Prims.of_int (3))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             FStarC_Tactics_InterpFuns.mk_tactic_interpretation_2
               "FStar.Tactics.TypeRepr.generate_up (plugin)"
               (FStarC_Tactics_Native.from_tactic_2 generate_up)
               FStarC_Syntax_Embeddings.e_string
               FStarC_Syntax_Embeddings.e_unit
               FStarC_Syntax_Embeddings.e_unit psc ncb us args)
let (make_implicits :
  FStar_Tactics_NamedView.binders -> FStar_Tactics_NamedView.binders) =
  fun bs ->
    FStar_List_Tot_Base.map
      (fun b ->
         match b.FStar_Tactics_NamedView.qual with
         | FStarC_Reflection_V2_Data.Q_Explicit ->
             {
               FStar_Tactics_NamedView.uniq =
                 (b.FStar_Tactics_NamedView.uniq);
               FStar_Tactics_NamedView.ppname =
                 (b.FStar_Tactics_NamedView.ppname);
               FStar_Tactics_NamedView.sort =
                 (b.FStar_Tactics_NamedView.sort);
               FStar_Tactics_NamedView.qual =
                 FStarC_Reflection_V2_Data.Q_Implicit;
               FStar_Tactics_NamedView.attrs =
                 (b.FStar_Tactics_NamedView.attrs)
             }
         | uu___ -> b) bs
let (binder_to_argv :
  FStar_Tactics_NamedView.binder -> FStarC_Reflection_V2_Data.argv) =
  fun b ->
    ((FStar_Tactics_V2_SyntaxCoercions.binder_to_term b),
      (b.FStar_Tactics_NamedView.qual))
let (generate_all :
  FStarC_Reflection_Types.name ->
    FStar_Tactics_NamedView.binders ->
      FStarC_Reflection_V2_Data.ctor Prims.list ->
        (FStarC_Reflection_Types.decls, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun nm ->
    fun params ->
      fun ctors ->
        let uu___ =
          Obj.magic
            (FStar_Tactics_Effect.lift_div_tac
               (fun uu___1 -> make_implicits params)) in
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.TypeRepr.fst"
                   (Prims.of_int (119)) (Prims.of_int (17))
                   (Prims.of_int (119)) (Prims.of_int (38)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.TypeRepr.fst"
                   (Prims.of_int (119)) (Prims.of_int (41))
                   (Prims.of_int (165)) (Prims.of_int (27)))))
          (Obj.magic uu___)
          (fun uu___1 ->
             (fun params_i ->
                let uu___1 =
                  Obj.magic
                    (FStar_Tactics_Effect.lift_div_tac
                       (fun uu___2 ->
                          FStar_Reflection_V2_Derived.mk_app
                            (FStar_Tactics_NamedView.pack
                               (FStar_Tactics_NamedView.Tv_FVar
                                  (FStarC_Reflection_V2_Builtins.pack_fv nm)))
                            (FStar_List_Tot_Base.map binder_to_argv params))) in
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "FStar.Tactics.TypeRepr.fst"
                              (Prims.of_int (120)) (Prims.of_int (15))
                              (Prims.of_int (120)) (Prims.of_int (88)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "FStar.Tactics.TypeRepr.fst"
                              (Prims.of_int (120)) (Prims.of_int (91))
                              (Prims.of_int (165)) (Prims.of_int (27)))))
                     (Obj.magic uu___1)
                     (fun uu___2 ->
                        (fun t ->
                           let uu___2 = generate_repr_typ params ctors in
                           Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "FStar.Tactics.TypeRepr.fst"
                                         (Prims.of_int (121))
                                         (Prims.of_int (15))
                                         (Prims.of_int (121))
                                         (Prims.of_int (45)))))
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "FStar.Tactics.TypeRepr.fst"
                                         (Prims.of_int (121))
                                         (Prims.of_int (48))
                                         (Prims.of_int (165))
                                         (Prims.of_int (27)))))
                                (Obj.magic uu___2)
                                (fun uu___3 ->
                                   (fun t_repr ->
                                      let uu___3 =
                                        let uu___4 =
                                          let uu___5 =
                                            let uu___6 =
                                              let uu___7 =
                                                let uu___8 =
                                                  FStar_Tactics_V2_SyntaxHelpers.mk_arr
                                                    params
                                                    (FStarC_Reflection_V2_Data.C_Total
                                                       (FStarC_Reflection_V2_Builtins.pack_ln
                                                          (FStarC_Reflection_V2_Data.Tv_Type
                                                             (FStarC_Reflection_V2_Builtins.pack_universe
                                                                FStarC_Reflection_V2_Data.Uv_Unk)))) in
                                                FStar_Tactics_Effect.tac_bind
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "FStar.Tactics.TypeRepr.fst"
                                                           (Prims.of_int (127))
                                                           (Prims.of_int (15))
                                                           (Prims.of_int (127))
                                                           (Prims.of_int (47)))))
                                                  (FStar_Sealed.seal
                                                     (Obj.magic
                                                        (FStar_Range.mk_range
                                                           "FStar.Tactics.TypeRepr.fst"
                                                           (Prims.of_int (125))
                                                           (Prims.of_int (6))
                                                           (Prims.of_int (128))
                                                           (Prims.of_int (36)))))
                                                  (Obj.magic uu___8)
                                                  (fun uu___9 ->
                                                     (fun uu___9 ->
                                                        let uu___10 =
                                                          FStar_Tactics_V2_Derived.mk_abs
                                                            params t_repr in
                                                        Obj.magic
                                                          (FStar_Tactics_Effect.tac_bind
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "FStar.Tactics.TypeRepr.fst"
                                                                    (Prims.of_int (128))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (128))
                                                                    (Prims.of_int (35)))))
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "FStar.Tactics.TypeRepr.fst"
                                                                    (Prims.of_int (125))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (128))
                                                                    (Prims.of_int (36)))))
                                                             (Obj.magic
                                                                uu___10)
                                                             (fun uu___11 ->
                                                                FStar_Tactics_Effect.lift_div_tac
                                                                  (fun
                                                                    uu___12
                                                                    ->
                                                                    {
                                                                    FStar_Tactics_NamedView.lb_fv
                                                                    =
                                                                    (FStarC_Reflection_V2_Builtins.pack_fv
                                                                    (add_suffix
                                                                    "_repr"
                                                                    nm));
                                                                    FStar_Tactics_NamedView.lb_us
                                                                    = [];
                                                                    FStar_Tactics_NamedView.lb_typ
                                                                    = uu___9;
                                                                    FStar_Tactics_NamedView.lb_def
                                                                    = uu___11
                                                                    }))))
                                                       uu___9) in
                                              FStar_Tactics_Effect.tac_bind
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "FStar.Tactics.TypeRepr.fst"
                                                         (Prims.of_int (125))
                                                         (Prims.of_int (6))
                                                         (Prims.of_int (128))
                                                         (Prims.of_int (36)))))
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "FStar.Tactics.TypeRepr.fst"
                                                         (Prims.of_int (124))
                                                         (Prims.of_int (10))
                                                         (Prims.of_int (129))
                                                         (Prims.of_int (6)))))
                                                (Obj.magic uu___7)
                                                (fun uu___8 ->
                                                   FStar_Tactics_Effect.lift_div_tac
                                                     (fun uu___9 -> [uu___8])) in
                                            FStar_Tactics_Effect.tac_bind
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "FStar.Tactics.TypeRepr.fst"
                                                       (Prims.of_int (124))
                                                       (Prims.of_int (10))
                                                       (Prims.of_int (129))
                                                       (Prims.of_int (6)))))
                                              (FStar_Sealed.seal
                                                 (Obj.magic
                                                    (FStar_Range.mk_range
                                                       "FStar.Tactics.TypeRepr.fst"
                                                       (Prims.of_int (123))
                                                       (Prims.of_int (4))
                                                       (Prims.of_int (129))
                                                       (Prims.of_int (6)))))
                                              (Obj.magic uu___6)
                                              (fun uu___7 ->
                                                 FStar_Tactics_Effect.lift_div_tac
                                                   (fun uu___8 ->
                                                      {
                                                        FStar_Tactics_NamedView.isrec
                                                          = false;
                                                        FStar_Tactics_NamedView.lbs
                                                          = uu___7
                                                      })) in
                                          FStar_Tactics_Effect.tac_bind
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "FStar.Tactics.TypeRepr.fst"
                                                     (Prims.of_int (123))
                                                     (Prims.of_int (4))
                                                     (Prims.of_int (129))
                                                     (Prims.of_int (6)))))
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "FStar.Tactics.TypeRepr.fst"
                                                     (Prims.of_int (122))
                                                     (Prims.of_int (31))
                                                     (Prims.of_int (130))
                                                     (Prims.of_int (3)))))
                                            (Obj.magic uu___5)
                                            (fun uu___6 ->
                                               FStar_Tactics_Effect.lift_div_tac
                                                 (fun uu___7 ->
                                                    FStar_Tactics_NamedView.Sg_Let
                                                      uu___6)) in
                                        FStar_Tactics_Effect.tac_bind
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "FStar.Tactics.TypeRepr.fst"
                                                   (Prims.of_int (122))
                                                   (Prims.of_int (31))
                                                   (Prims.of_int (130))
                                                   (Prims.of_int (3)))))
                                          (FStar_Sealed.seal
                                             (Obj.magic
                                                (FStar_Range.mk_range
                                                   "FStar.Tactics.TypeRepr.fst"
                                                   (Prims.of_int (122))
                                                   (Prims.of_int (16))
                                                   (Prims.of_int (130))
                                                   (Prims.of_int (3)))))
                                          (Obj.magic uu___4)
                                          (fun uu___5 ->
                                             (fun uu___5 ->
                                                Obj.magic
                                                  (FStar_Tactics_NamedView.pack_sigelt
                                                     uu___5)) uu___5) in
                                      Obj.magic
                                        (FStar_Tactics_Effect.tac_bind
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "FStar.Tactics.TypeRepr.fst"
                                                    (Prims.of_int (122))
                                                    (Prims.of_int (16))
                                                    (Prims.of_int (130))
                                                    (Prims.of_int (3)))))
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "FStar.Tactics.TypeRepr.fst"
                                                    (Prims.of_int (131))
                                                    (Prims.of_int (4))
                                                    (Prims.of_int (165))
                                                    (Prims.of_int (27)))))
                                           (Obj.magic uu___3)
                                           (fun uu___4 ->
                                              (fun se_repr ->
                                                 let uu___4 =
                                                   Obj.magic
                                                     (FStar_Tactics_Effect.lift_div_tac
                                                        (fun uu___5 ->
                                                           FStarC_Reflection_V2_Builtins.pack_ln
                                                             (FStarC_Reflection_V2_Data.Tv_App
                                                                ((FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (
                                                                    FStarC_Reflection_V2_Data.Tv_FVar
                                                                    (FStarC_Reflection_V2_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "Effect";
                                                                    "synth_by_tactic"]))),
                                                                  ((FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_Abs
                                                                    ((FStarC_Reflection_V2_Builtins.pack_binder
                                                                    {
                                                                    FStarC_Reflection_V2_Data.sort2
                                                                    =
                                                                    (FStarC_Reflection_V2_Builtins.pack_ln
                                                                    FStarC_Reflection_V2_Data.Tv_Unknown);
                                                                    FStarC_Reflection_V2_Data.qual
                                                                    =
                                                                    FStarC_Reflection_V2_Data.Q_Explicit;
                                                                    FStarC_Reflection_V2_Data.attrs
                                                                    = [];
                                                                    FStarC_Reflection_V2_Data.ppname2
                                                                    =
                                                                    (FStar_Sealed.seal
                                                                    "uu___")
                                                                    }),
                                                                    (FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_App
                                                                    ((FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_FVar
                                                                    (FStarC_Reflection_V2_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "TypeRepr";
                                                                    "generate_down"]))),
                                                                    ((FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_Const
                                                                    FStarC_Reflection_V2_Data.C_Unit)),
                                                                    FStarC_Reflection_V2_Data.Q_Explicit))))))),
                                                                    FStarC_Reflection_V2_Data.Q_Explicit))))) in
                                                 Obj.magic
                                                   (FStar_Tactics_Effect.tac_bind
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "FStar.Tactics.TypeRepr.fst"
                                                               (Prims.of_int (134))
                                                               (Prims.of_int (4))
                                                               (Prims.of_int (134))
                                                               (Prims.of_int (30)))))
                                                      (FStar_Sealed.seal
                                                         (Obj.magic
                                                            (FStar_Range.mk_range
                                                               "FStar.Tactics.TypeRepr.fst"
                                                               (Prims.of_int (135))
                                                               (Prims.of_int (4))
                                                               (Prims.of_int (165))
                                                               (Prims.of_int (27)))))
                                                      (Obj.magic uu___4)
                                                      (fun uu___5 ->
                                                         (fun down_def ->
                                                            let uu___5 =
                                                              FStar_Tactics_V2_Derived.mk_abs
                                                                params_i
                                                                down_def in
                                                            Obj.magic
                                                              (FStar_Tactics_Effect.tac_bind
                                                                 (FStar_Sealed.seal
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.TypeRepr.fst"
                                                                    (Prims.of_int (136))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (136))
                                                                    (Prims.of_int (41)))))
                                                                 (FStar_Sealed.seal
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.TypeRepr.fst"
                                                                    (Prims.of_int (136))
                                                                    (Prims.of_int (44))
                                                                    (Prims.of_int (165))
                                                                    (Prims.of_int (27)))))
                                                                 (Obj.magic
                                                                    uu___5)
                                                                 (fun uu___6
                                                                    ->
                                                                    (fun
                                                                    down_def1
                                                                    ->
                                                                    let uu___6
                                                                    =
                                                                    let uu___7
                                                                    =
                                                                    FStar_Tactics_V2_Derived.fresh_binder
                                                                    t in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.TypeRepr.fst"
                                                                    (Prims.of_int (138))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (138))
                                                                    (Prims.of_int (26)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.TypeRepr.fst"
                                                                    (Prims.of_int (139))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (147))
                                                                    (Prims.of_int (3)))))
                                                                    (Obj.magic
                                                                    uu___7)
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun b ->
                                                                    let uu___8
                                                                    =
                                                                    let uu___9
                                                                    =
                                                                    let uu___10
                                                                    =
                                                                    let uu___11
                                                                    =
                                                                    let uu___12
                                                                    =
                                                                    FStar_Tactics_V2_SyntaxHelpers.mk_tot_arr
                                                                    params_i
                                                                    (FStar_Tactics_NamedView.pack
                                                                    (FStar_Tactics_NamedView.Tv_Arrow
                                                                    (b,
                                                                    (FStarC_Reflection_V2_Data.C_Total
                                                                    t_repr)))) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.TypeRepr.fst"
                                                                    (Prims.of_int (144))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (144))
                                                                    (Prims.of_int (67)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.TypeRepr.fst"
                                                                    (Prims.of_int (142))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (145))
                                                                    (Prims.of_int (26)))))
                                                                    (Obj.magic
                                                                    uu___12)
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    {
                                                                    FStar_Tactics_NamedView.lb_fv
                                                                    =
                                                                    (FStarC_Reflection_V2_Builtins.pack_fv
                                                                    (add_suffix
                                                                    "_down"
                                                                    nm));
                                                                    FStar_Tactics_NamedView.lb_us
                                                                    = [];
                                                                    FStar_Tactics_NamedView.lb_typ
                                                                    = uu___13;
                                                                    FStar_Tactics_NamedView.lb_def
                                                                    =
                                                                    down_def1
                                                                    })) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.TypeRepr.fst"
                                                                    (Prims.of_int (142))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (145))
                                                                    (Prims.of_int (26)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.TypeRepr.fst"
                                                                    (Prims.of_int (141))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (146))
                                                                    (Prims.of_int (8)))))
                                                                    (Obj.magic
                                                                    uu___11)
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    [uu___12])) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.TypeRepr.fst"
                                                                    (Prims.of_int (141))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (146))
                                                                    (Prims.of_int (8)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.TypeRepr.fst"
                                                                    (Prims.of_int (140))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (146))
                                                                    (Prims.of_int (8)))))
                                                                    (Obj.magic
                                                                    uu___10)
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    {
                                                                    FStar_Tactics_NamedView.isrec
                                                                    = false;
                                                                    FStar_Tactics_NamedView.lbs
                                                                    = uu___11
                                                                    })) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.TypeRepr.fst"
                                                                    (Prims.of_int (140))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (146))
                                                                    (Prims.of_int (8)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.TypeRepr.fst"
                                                                    (Prims.of_int (139))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (147))
                                                                    (Prims.of_int (3)))))
                                                                    (Obj.magic
                                                                    uu___9)
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    FStar_Tactics_NamedView.Sg_Let
                                                                    uu___10)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.TypeRepr.fst"
                                                                    (Prims.of_int (139))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (147))
                                                                    (Prims.of_int (3)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.TypeRepr.fst"
                                                                    (Prims.of_int (139))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (147))
                                                                    (Prims.of_int (3)))))
                                                                    (Obj.magic
                                                                    uu___8)
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun
                                                                    uu___9 ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_NamedView.pack_sigelt
                                                                    uu___9))
                                                                    uu___9)))
                                                                    uu___8) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.TypeRepr.fst"
                                                                    (Prims.of_int (137))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (147))
                                                                    (Prims.of_int (3)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.TypeRepr.fst"
                                                                    (Prims.of_int (148))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (165))
                                                                    (Prims.of_int (27)))))
                                                                    (Obj.magic
                                                                    uu___6)
                                                                    (fun
                                                                    uu___7 ->
                                                                    (fun
                                                                    se_down
                                                                    ->
                                                                    let uu___7
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_App
                                                                    ((FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_FVar
                                                                    (FStarC_Reflection_V2_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "Effect";
                                                                    "synth_by_tactic"]))),
                                                                    ((FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_Abs
                                                                    ((FStarC_Reflection_V2_Builtins.pack_binder
                                                                    {
                                                                    FStarC_Reflection_V2_Data.sort2
                                                                    =
                                                                    (FStarC_Reflection_V2_Builtins.pack_ln
                                                                    FStarC_Reflection_V2_Data.Tv_Unknown);
                                                                    FStarC_Reflection_V2_Data.qual
                                                                    =
                                                                    FStarC_Reflection_V2_Data.Q_Explicit;
                                                                    FStarC_Reflection_V2_Data.attrs
                                                                    = [];
                                                                    FStarC_Reflection_V2_Data.ppname2
                                                                    =
                                                                    (FStar_Sealed.seal
                                                                    "uu___")
                                                                    }),
                                                                    (FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_App
                                                                    ((FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_App
                                                                    ((FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_FVar
                                                                    (FStarC_Reflection_V2_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "TypeRepr";
                                                                    "generate_up"]))),
                                                                    ((FStar_Tactics_NamedView.pack
                                                                    (FStar_Tactics_NamedView.Tv_Const
                                                                    (FStarC_Reflection_V2_Data.C_String
                                                                    (FStarC_Reflection_V2_Builtins.implode_qn
                                                                    nm)))),
                                                                    FStarC_Reflection_V2_Data.Q_Explicit)))),
                                                                    ((FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_Const
                                                                    FStarC_Reflection_V2_Data.C_Unit)),
                                                                    FStarC_Reflection_V2_Data.Q_Explicit))))))),
                                                                    FStarC_Reflection_V2_Data.Q_Explicit))))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.TypeRepr.fst"
                                                                    (Prims.of_int (150))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (150))
                                                                    (Prims.of_int (77)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.TypeRepr.fst"
                                                                    (Prims.of_int (151))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (165))
                                                                    (Prims.of_int (27)))))
                                                                    (Obj.magic
                                                                    uu___7)
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun
                                                                    up_def ->
                                                                    let uu___8
                                                                    =
                                                                    FStar_Tactics_V2_Derived.mk_abs
                                                                    params_i
                                                                    up_def in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.TypeRepr.fst"
                                                                    (Prims.of_int (152))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (152))
                                                                    (Prims.of_int (37)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.TypeRepr.fst"
                                                                    (Prims.of_int (152))
                                                                    (Prims.of_int (40))
                                                                    (Prims.of_int (165))
                                                                    (Prims.of_int (27)))))
                                                                    (Obj.magic
                                                                    uu___8)
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun
                                                                    up_def1
                                                                    ->
                                                                    let uu___9
                                                                    =
                                                                    let uu___10
                                                                    =
                                                                    FStar_Tactics_V2_Derived.fresh_binder
                                                                    t_repr in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.TypeRepr.fst"
                                                                    (Prims.of_int (154))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (154))
                                                                    (Prims.of_int (31)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.TypeRepr.fst"
                                                                    (Prims.of_int (155))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (163))
                                                                    (Prims.of_int (3)))))
                                                                    (Obj.magic
                                                                    uu___10)
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    (fun b ->
                                                                    let uu___11
                                                                    =
                                                                    let uu___12
                                                                    =
                                                                    let uu___13
                                                                    =
                                                                    let uu___14
                                                                    =
                                                                    let uu___15
                                                                    =
                                                                    FStar_Tactics_V2_SyntaxHelpers.mk_tot_arr
                                                                    params_i
                                                                    (FStar_Tactics_NamedView.pack
                                                                    (FStar_Tactics_NamedView.Tv_Arrow
                                                                    (b,
                                                                    (FStarC_Reflection_V2_Data.C_Total
                                                                    t)))) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.TypeRepr.fst"
                                                                    (Prims.of_int (160))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (160))
                                                                    (Prims.of_int (62)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.TypeRepr.fst"
                                                                    (Prims.of_int (158))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (161))
                                                                    (Prims.of_int (24)))))
                                                                    (Obj.magic
                                                                    uu___15)
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___17
                                                                    ->
                                                                    {
                                                                    FStar_Tactics_NamedView.lb_fv
                                                                    =
                                                                    (FStarC_Reflection_V2_Builtins.pack_fv
                                                                    (add_suffix
                                                                    "_up" nm));
                                                                    FStar_Tactics_NamedView.lb_us
                                                                    = [];
                                                                    FStar_Tactics_NamedView.lb_typ
                                                                    = uu___16;
                                                                    FStar_Tactics_NamedView.lb_def
                                                                    = up_def1
                                                                    })) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.TypeRepr.fst"
                                                                    (Prims.of_int (158))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (161))
                                                                    (Prims.of_int (24)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.TypeRepr.fst"
                                                                    (Prims.of_int (157))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (162))
                                                                    (Prims.of_int (8)))))
                                                                    (Obj.magic
                                                                    uu___14)
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    [uu___15])) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.TypeRepr.fst"
                                                                    (Prims.of_int (157))
                                                                    (Prims.of_int (12))
                                                                    (Prims.of_int (162))
                                                                    (Prims.of_int (8)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.TypeRepr.fst"
                                                                    (Prims.of_int (156))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (162))
                                                                    (Prims.of_int (8)))))
                                                                    (Obj.magic
                                                                    uu___13)
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    {
                                                                    FStar_Tactics_NamedView.isrec
                                                                    = false;
                                                                    FStar_Tactics_NamedView.lbs
                                                                    = uu___14
                                                                    })) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.TypeRepr.fst"
                                                                    (Prims.of_int (156))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (162))
                                                                    (Prims.of_int (8)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.TypeRepr.fst"
                                                                    (Prims.of_int (155))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (163))
                                                                    (Prims.of_int (3)))))
                                                                    (Obj.magic
                                                                    uu___12)
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    FStar_Tactics_NamedView.Sg_Let
                                                                    uu___13)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.TypeRepr.fst"
                                                                    (Prims.of_int (155))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (163))
                                                                    (Prims.of_int (3)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.TypeRepr.fst"
                                                                    (Prims.of_int (155))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (163))
                                                                    (Prims.of_int (3)))))
                                                                    (Obj.magic
                                                                    uu___11)
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_NamedView.pack_sigelt
                                                                    uu___12))
                                                                    uu___12)))
                                                                    uu___11) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.TypeRepr.fst"
                                                                    (Prims.of_int (153))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (163))
                                                                    (Prims.of_int (3)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.TypeRepr.fst"
                                                                    (Prims.of_int (165))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (165))
                                                                    (Prims.of_int (27)))))
                                                                    (Obj.magic
                                                                    uu___9)
                                                                    (fun
                                                                    se_up ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    [se_repr;
                                                                    se_down;
                                                                    se_up]))))
                                                                    uu___9)))
                                                                    uu___8)))
                                                                    uu___7)))
                                                                    uu___6)))
                                                           uu___5))) uu___4)))
                                     uu___3))) uu___2))) uu___1)
let (entry :
  Prims.string ->
    (FStarC_Reflection_Types.decls, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun nm ->
    let uu___ = get_inductive_typ nm in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.TypeRepr.fst"
               (Prims.of_int (169)) (Prims.of_int (41)) (Prims.of_int (169))
               (Prims.of_int (61)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.TypeRepr.fst"
               (Prims.of_int (168)) (Prims.of_int (37)) (Prims.of_int (170))
               (Prims.of_int (30))))) (Obj.magic uu___)
      (fun uu___1 ->
         (fun uu___1 ->
            match uu___1 with
            | FStar_Tactics_NamedView.Sg_Inductive
                { FStar_Tactics_NamedView.nm = nm1;
                  FStar_Tactics_NamedView.univs1 = uu___2;
                  FStar_Tactics_NamedView.params = params;
                  FStar_Tactics_NamedView.typ = uu___3;
                  FStar_Tactics_NamedView.ctors = ctors;_}
                -> Obj.magic (generate_all nm1 params ctors)) uu___1)
let _ =
  FStarC_Tactics_Native.register_tactic "FStar.Tactics.TypeRepr.entry"
    (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.TypeRepr.entry (plugin)"
               (FStarC_Tactics_Native.from_tactic_1 entry)
               FStarC_Syntax_Embeddings.e_string
               (FStarC_Syntax_Embeddings.e_list
                  FStarC_Reflection_V2_Embeddings.e_sigelt) psc ncb us args)