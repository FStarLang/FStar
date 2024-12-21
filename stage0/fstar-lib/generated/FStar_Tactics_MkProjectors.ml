open Prims
exception NotFound 
let (uu___is_NotFound : Prims.exn -> Prims.bool) =
  fun projectee -> match projectee with | NotFound -> true | uu___ -> false
let (debug :
  (unit -> (Prims.string, unit) FStar_Tactics_Effect.tac_repr) ->
    (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun f ->
    let uu___ = FStarC_Tactics_V2_Builtins.debugging () in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.MkProjectors.fst"
               (Prims.of_int (23)) (Prims.of_int (5)) (Prims.of_int (23))
               (Prims.of_int (17)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.MkProjectors.fst"
               (Prims.of_int (23)) (Prims.of_int (2)) (Prims.of_int (24))
               (Prims.of_int (16))))) (Obj.magic uu___)
      (fun uu___1 ->
         (fun uu___1 ->
            if uu___1
            then
              Obj.magic
                (Obj.repr
                   (let uu___2 = f () in
                    FStar_Tactics_Effect.tac_bind
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range
                               "FStar.Tactics.MkProjectors.fst"
                               (Prims.of_int (24)) (Prims.of_int (10))
                               (Prims.of_int (24)) (Prims.of_int (16)))))
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range
                               "FStar.Tactics.MkProjectors.fst"
                               (Prims.of_int (24)) (Prims.of_int (4))
                               (Prims.of_int (24)) (Prims.of_int (16)))))
                      (Obj.magic uu___2)
                      (fun uu___3 ->
                         (fun uu___3 ->
                            Obj.magic
                              (FStarC_Tactics_V2_Builtins.print uu___3))
                           uu___3)))
            else
              Obj.magic
                (Obj.repr
                   (FStar_Tactics_Effect.lift_div_tac (fun uu___3 -> ()))))
           uu___1)
let (mk_one_projector :
  Prims.string Prims.list ->
    Prims.nat -> Prims.nat -> (unit, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun unf ->
    fun np ->
      fun i ->
        let uu___ =
          debug
            (fun uu___1 ->
               let uu___2 =
                 FStarC_Tactics_V2_Builtins.dump "ENTRY mk_one_projector" in
               FStar_Tactics_Effect.tac_bind
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "FStar.Tactics.MkProjectors.fst"
                          (Prims.of_int (28)) (Prims.of_int (19))
                          (Prims.of_int (28)) (Prims.of_int (48)))))
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "FStar.Tactics.MkProjectors.fst"
                          (Prims.of_int (28)) (Prims.of_int (50))
                          (Prims.of_int (28)) (Prims.of_int (52)))))
                 (Obj.magic uu___2)
                 (fun uu___3 ->
                    FStar_Tactics_Effect.lift_div_tac (fun uu___4 -> ""))) in
        FStar_Tactics_Effect.tac_bind
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.MkProjectors.fst"
                   (Prims.of_int (28)) (Prims.of_int (2)) (Prims.of_int (28))
                   (Prims.of_int (53)))))
          (FStar_Sealed.seal
             (Obj.magic
                (FStar_Range.mk_range "FStar.Tactics.MkProjectors.fst"
                   (Prims.of_int (28)) (Prims.of_int (54))
                   (Prims.of_int (48)) (Prims.of_int (41)))))
          (Obj.magic uu___)
          (fun uu___1 ->
             (fun uu___1 ->
                let uu___2 = FStarC_Tactics_V2_Builtins.intros np in
                Obj.magic
                  (FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "FStar.Tactics.MkProjectors.fst"
                              (Prims.of_int (29)) (Prims.of_int (16))
                              (Prims.of_int (29)) (Prims.of_int (51)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range
                              "FStar.Tactics.MkProjectors.fst"
                              (Prims.of_int (29)) (Prims.of_int (54))
                              (Prims.of_int (48)) (Prims.of_int (41)))))
                     (Obj.magic uu___2)
                     (fun uu___3 ->
                        (fun _params ->
                           let uu___3 = FStarC_Tactics_V2_Builtins.intro () in
                           Obj.magic
                             (FStar_Tactics_Effect.tac_bind
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "FStar.Tactics.MkProjectors.fst"
                                         (Prims.of_int (30))
                                         (Prims.of_int (24))
                                         (Prims.of_int (30))
                                         (Prims.of_int (32)))))
                                (FStar_Sealed.seal
                                   (Obj.magic
                                      (FStar_Range.mk_range
                                         "FStar.Tactics.MkProjectors.fst"
                                         (Prims.of_int (30))
                                         (Prims.of_int (35))
                                         (Prims.of_int (48))
                                         (Prims.of_int (41)))))
                                (Obj.magic uu___3)
                                (fun uu___4 ->
                                   (fun thing ->
                                      let uu___4 =
                                        FStarC_Tactics_V2_Builtins.t_destruct
                                          (FStar_Tactics_V2_SyntaxCoercions.binding_to_term
                                             thing) in
                                      Obj.magic
                                        (FStar_Tactics_Effect.tac_bind
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "FStar.Tactics.MkProjectors.fst"
                                                    (Prims.of_int (31))
                                                    (Prims.of_int (10))
                                                    (Prims.of_int (31))
                                                    (Prims.of_int (26)))))
                                           (FStar_Sealed.seal
                                              (Obj.magic
                                                 (FStar_Range.mk_range
                                                    "FStar.Tactics.MkProjectors.fst"
                                                    (Prims.of_int (32))
                                                    (Prims.of_int (2))
                                                    (Prims.of_int (48))
                                                    (Prims.of_int (41)))))
                                           (Obj.magic uu___4)
                                           (fun uu___5 ->
                                              (fun r ->
                                                 match r with
                                                 | (cons, arity)::[] ->
                                                     Obj.magic
                                                       (Obj.repr
                                                          (let uu___5 =
                                                             if i >= arity
                                                             then
                                                               Obj.magic
                                                                 (FStar_Tactics_V2_Derived.fail
                                                                    "proj: bad index in mk_one_projector")
                                                             else
                                                               Obj.magic
                                                                 (FStar_Tactics_Effect.lift_div_tac
                                                                    (
                                                                    fun
                                                                    uu___7 ->
                                                                    ())) in
                                                           FStar_Tactics_Effect.tac_bind
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (34))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (48)))))
                                                             (FStar_Sealed.seal
                                                                (Obj.magic
                                                                   (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (49))
                                                                    (Prims.of_int (46))
                                                                    (Prims.of_int (15)))))
                                                             (Obj.magic
                                                                uu___5)
                                                             (fun uu___6 ->
                                                                (fun uu___6
                                                                   ->
                                                                   let uu___7
                                                                    =
                                                                    FStarC_Tactics_V2_Builtins.intros
                                                                    i in
                                                                   Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (36))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (36))
                                                                    (Prims.of_int (51)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (36))
                                                                    (Prims.of_int (54))
                                                                    (Prims.of_int (46))
                                                                    (Prims.of_int (15)))))
                                                                    (Obj.magic
                                                                    uu___7)
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun
                                                                    uu___8 ->
                                                                    let uu___9
                                                                    =
                                                                    FStarC_Tactics_V2_Builtins.intro
                                                                    () in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (37))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (37))
                                                                    (Prims.of_int (25)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (37))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (46))
                                                                    (Prims.of_int (15)))))
                                                                    (Obj.magic
                                                                    uu___9)
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun
                                                                    the_b ->
                                                                    let uu___10
                                                                    =
                                                                    FStarC_Tactics_V2_Builtins.intros
                                                                    ((arity -
                                                                    i) -
                                                                    Prims.int_one) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (38))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (38))
                                                                    (Prims.of_int (61)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (38))
                                                                    (Prims.of_int (64))
                                                                    (Prims.of_int (46))
                                                                    (Prims.of_int (15)))))
                                                                    (Obj.magic
                                                                    uu___10)
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    let uu___12
                                                                    =
                                                                    FStarC_Tactics_V2_Builtins.intro
                                                                    () in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (39))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (39))
                                                                    (Prims.of_int (35)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (40))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (46))
                                                                    (Prims.of_int (15)))))
                                                                    (Obj.magic
                                                                    uu___12)
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    (fun eq_b
                                                                    ->
                                                                    let uu___13
                                                                    =
                                                                    FStarC_Tactics_V2_Builtins.rewrite
                                                                    eq_b in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (40))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (40))
                                                                    (Prims.of_int (16)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (46))
                                                                    (Prims.of_int (15)))))
                                                                    (Obj.magic
                                                                    uu___13)
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    let uu___15
                                                                    =
                                                                    FStarC_Tactics_V2_Builtins.norm
                                                                    [FStar_Pervasives.iota;
                                                                    FStar_Pervasives.delta_only
                                                                    unf;
                                                                    FStar_Pervasives.zeta_full] in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (42)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (46))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (46))
                                                                    (Prims.of_int (15)))))
                                                                    (Obj.magic
                                                                    uu___15)
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_V2_Derived.exact
                                                                    (FStar_Tactics_V2_SyntaxCoercions.binding_to_term
                                                                    the_b)))
                                                                    uu___16)))
                                                                    uu___14)))
                                                                    uu___13)))
                                                                    uu___11)))
                                                                    uu___10)))
                                                                    uu___8)))
                                                                  uu___6)))
                                                 | uu___5 ->
                                                     Obj.magic
                                                       (Obj.repr
                                                          (FStar_Tactics_V2_Derived.fail
                                                             "proj: more than one case?")))
                                                uu___5))) uu___4))) uu___3)))
               uu___1)
let _ =
  FStarC_Tactics_Native.register_tactic
    "FStar.Tactics.MkProjectors.mk_one_projector" (Prims.of_int (4))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             FStarC_Tactics_InterpFuns.mk_tactic_interpretation_3
               "FStar.Tactics.MkProjectors.mk_one_projector (plugin)"
               (FStarC_Tactics_Native.from_tactic_3 mk_one_projector)
               (FStarC_Syntax_Embeddings.e_list
                  FStarC_Syntax_Embeddings.e_string)
               FStarC_Syntax_Embeddings.e_int FStarC_Syntax_Embeddings.e_int
               FStarC_Syntax_Embeddings.e_unit psc ncb us args)
let (mk_one_method :
  Prims.string -> Prims.nat -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun proj ->
    fun np ->
      let uu___ =
        debug
          (fun uu___1 ->
             let uu___2 =
               FStarC_Tactics_V2_Builtins.dump "ENTRY mk_one_method" in
             FStar_Tactics_Effect.tac_bind
               (FStar_Sealed.seal
                  (Obj.magic
                     (FStar_Range.mk_range "FStar.Tactics.MkProjectors.fst"
                        (Prims.of_int (52)) (Prims.of_int (19))
                        (Prims.of_int (52)) (Prims.of_int (45)))))
               (FStar_Sealed.seal
                  (Obj.magic
                     (FStar_Range.mk_range "FStar.Tactics.MkProjectors.fst"
                        (Prims.of_int (52)) (Prims.of_int (47))
                        (Prims.of_int (52)) (Prims.of_int (49)))))
               (Obj.magic uu___2)
               (fun uu___3 ->
                  FStar_Tactics_Effect.lift_div_tac (fun uu___4 -> ""))) in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.MkProjectors.fst"
                 (Prims.of_int (52)) (Prims.of_int (2)) (Prims.of_int (52))
                 (Prims.of_int (50)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.MkProjectors.fst"
                 (Prims.of_int (52)) (Prims.of_int (51)) (Prims.of_int (58))
                 (Prims.of_int (70))))) (Obj.magic uu___)
        (fun uu___1 ->
           (fun uu___1 ->
              let uu___2 =
                Obj.magic
                  (FStar_Tactics_Effect.lift_div_tac
                     (fun uu___3 ->
                        FStarC_Reflection_V2_Builtins.explode_qn proj)) in
              Obj.magic
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range
                            "FStar.Tactics.MkProjectors.fst"
                            (Prims.of_int (53)) (Prims.of_int (11))
                            (Prims.of_int (53)) (Prims.of_int (26)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range
                            "FStar.Tactics.MkProjectors.fst"
                            (Prims.of_int (53)) (Prims.of_int (29))
                            (Prims.of_int (58)) (Prims.of_int (70)))))
                   (Obj.magic uu___2)
                   (fun uu___3 ->
                      (fun nm ->
                         let uu___3 =
                           FStar_Tactics_Util.repeatn np
                             (fun uu___4 ->
                                let uu___5 =
                                  FStarC_Tactics_V2_Builtins.intro () in
                                FStar_Tactics_Effect.tac_bind
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "FStar.Tactics.MkProjectors.fst"
                                           (Prims.of_int (54))
                                           (Prims.of_int (55))
                                           (Prims.of_int (54))
                                           (Prims.of_int (63)))))
                                  (FStar_Sealed.seal
                                     (Obj.magic
                                        (FStar_Range.mk_range
                                           "FStar.Tactics.MkProjectors.fst"
                                           (Prims.of_int (55))
                                           (Prims.of_int (37))
                                           (Prims.of_int (55))
                                           (Prims.of_int (68)))))
                                  (Obj.magic uu___5)
                                  (fun b ->
                                     FStar_Tactics_Effect.lift_div_tac
                                       (fun uu___6 ->
                                          ((FStar_Tactics_V2_SyntaxCoercions.binding_to_term
                                              b),
                                            FStarC_Reflection_V2_Data.Q_Implicit)))) in
                         Obj.magic
                           (FStar_Tactics_Effect.tac_bind
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "FStar.Tactics.MkProjectors.fst"
                                       (Prims.of_int (54))
                                       (Prims.of_int (15))
                                       (Prims.of_int (55))
                                       (Prims.of_int (69)))))
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "FStar.Tactics.MkProjectors.fst"
                                       (Prims.of_int (55))
                                       (Prims.of_int (72))
                                       (Prims.of_int (58))
                                       (Prims.of_int (70)))))
                              (Obj.magic uu___3)
                              (fun uu___4 ->
                                 (fun params ->
                                    let uu___4 =
                                      FStarC_Tactics_V2_Builtins.intro () in
                                    Obj.magic
                                      (FStar_Tactics_Effect.tac_bind
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "FStar.Tactics.MkProjectors.fst"
                                                  (Prims.of_int (56))
                                                  (Prims.of_int (24))
                                                  (Prims.of_int (56))
                                                  (Prims.of_int (32)))))
                                         (FStar_Sealed.seal
                                            (Obj.magic
                                               (FStar_Range.mk_range
                                                  "FStar.Tactics.MkProjectors.fst"
                                                  (Prims.of_int (56))
                                                  (Prims.of_int (35))
                                                  (Prims.of_int (58))
                                                  (Prims.of_int (70)))))
                                         (Obj.magic uu___4)
                                         (fun uu___5 ->
                                            (fun thing ->
                                               let uu___5 =
                                                 Obj.magic
                                                   (FStar_Tactics_Effect.lift_div_tac
                                                      (fun uu___6 ->
                                                         FStar_Tactics_NamedView.pack
                                                           (FStar_Tactics_NamedView.Tv_FVar
                                                              (FStarC_Reflection_V2_Builtins.pack_fv
                                                                 nm)))) in
                                               Obj.magic
                                                 (FStar_Tactics_Effect.tac_bind
                                                    (FStar_Sealed.seal
                                                       (Obj.magic
                                                          (FStar_Range.mk_range
                                                             "FStar.Tactics.MkProjectors.fst"
                                                             (Prims.of_int (57))
                                                             (Prims.of_int (13))
                                                             (Prims.of_int (57))
                                                             (Prims.of_int (40)))))
                                                    (FStar_Sealed.seal
                                                       (Obj.magic
                                                          (FStar_Range.mk_range
                                                             "FStar.Tactics.MkProjectors.fst"
                                                             (Prims.of_int (58))
                                                             (Prims.of_int (2))
                                                             (Prims.of_int (58))
                                                             (Prims.of_int (70)))))
                                                    (Obj.magic uu___5)
                                                    (fun uu___6 ->
                                                       (fun proj1 ->
                                                          Obj.magic
                                                            (FStar_Tactics_V2_Derived.exact
                                                               (FStar_Reflection_V2_Derived.mk_app
                                                                  proj1
                                                                  (FStar_List_Tot_Base.op_At
                                                                    params
                                                                    [
                                                                    ((FStar_Tactics_V2_SyntaxCoercions.binding_to_term
                                                                    thing),
                                                                    FStarC_Reflection_V2_Data.Q_Explicit)]))))
                                                         uu___6))) uu___5)))
                                   uu___4))) uu___3))) uu___1)
let _ =
  FStarC_Tactics_Native.register_tactic
    "FStar.Tactics.MkProjectors.mk_one_method" (Prims.of_int (3))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             FStarC_Tactics_InterpFuns.mk_tactic_interpretation_2
               "FStar.Tactics.MkProjectors.mk_one_method (plugin)"
               (FStarC_Tactics_Native.from_tactic_2 mk_one_method)
               FStarC_Syntax_Embeddings.e_string
               FStarC_Syntax_Embeddings.e_int FStarC_Syntax_Embeddings.e_unit
               psc ncb us args)
let (subst_map :
  (FStar_Tactics_NamedView.namedv * FStarC_Reflection_Types.fv) Prims.list ->
    FStar_Tactics_NamedView.term ->
      FStar_Tactics_NamedView.term ->
        (FStar_Tactics_NamedView.term, unit) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___2 ->
    fun uu___1 ->
      fun uu___ ->
        (fun ss ->
           fun r ->
             fun t ->
               Obj.magic
                 (FStar_Tactics_Effect.lift_div_tac
                    (fun uu___ ->
                       FStarC_Reflection_V2_Builtins.subst_term
                         (FStar_List_Tot_Base.map
                            (fun uu___1 ->
                               match uu___1 with
                               | (x, fv) ->
                                   FStarC_Syntax_Syntax.NT
                                     ((FStarC_Reflection_V2_Builtins.pack_namedv
                                         x),
                                       (FStar_Reflection_V2_Derived.mk_e_app
                                          (FStar_Tactics_NamedView.pack
                                             (FStar_Tactics_NamedView.Tv_FVar
                                                fv)) [r]))) ss) t))) uu___2
          uu___1 uu___
let (binder_mk_implicit :
  FStar_Tactics_NamedView.binder -> FStar_Tactics_NamedView.binder) =
  fun b ->
    let q =
      match b.FStar_Tactics_NamedView.qual with
      | FStarC_Reflection_V2_Data.Q_Explicit ->
          FStarC_Reflection_V2_Data.Q_Implicit
      | q1 -> q1 in
    {
      FStar_Tactics_NamedView.uniq = (b.FStar_Tactics_NamedView.uniq);
      FStar_Tactics_NamedView.ppname = (b.FStar_Tactics_NamedView.ppname);
      FStar_Tactics_NamedView.sort = (b.FStar_Tactics_NamedView.sort);
      FStar_Tactics_NamedView.qual = q;
      FStar_Tactics_NamedView.attrs = (b.FStar_Tactics_NamedView.attrs)
    }
let (binder_to_term :
  FStar_Tactics_NamedView.binder -> FStar_Tactics_NamedView.term) =
  fun b ->
    FStar_Tactics_NamedView.pack
      (FStar_Tactics_NamedView.Tv_Var
         (FStar_Tactics_V2_SyntaxCoercions.binder_to_namedv b))
let (binder_argv :
  FStar_Tactics_NamedView.binder -> FStarC_Reflection_V2_Data.argv) =
  fun b ->
    let q =
      match b.FStar_Tactics_NamedView.qual with
      | FStarC_Reflection_V2_Data.Q_Meta uu___ ->
          FStarC_Reflection_V2_Data.Q_Implicit
      | q1 -> q1 in
    ((binder_to_term b), q)
let rec list_last :
  'a . 'a Prims.list -> ('a, unit) FStar_Tactics_Effect.tac_repr =
  fun uu___ ->
    (fun xs ->
       match xs with
       | [] ->
           Obj.magic
             (Obj.repr (FStar_Tactics_V2_Derived.fail "list_last: empty"))
       | x::[] ->
           Obj.magic
             (Obj.repr (FStar_Tactics_Effect.lift_div_tac (fun uu___ -> x)))
       | uu___::xs1 -> Obj.magic (Obj.repr (list_last xs1))) uu___
let (embed_int : Prims.int -> FStar_Tactics_NamedView.term) =
  fun i ->
    FStarC_Reflection_V2_Builtins.pack_ln
      (FStarC_Reflection_V2_Data.Tv_Const (FStarC_Reflection_V2_Data.C_Int i))
let (embed_string : Prims.string -> FStar_Tactics_NamedView.term) =
  fun s ->
    FStarC_Reflection_V2_Builtins.pack_ln
      (FStarC_Reflection_V2_Data.Tv_Const
         (FStarC_Reflection_V2_Data.C_String s))
let (substitute_attr : FStar_Tactics_NamedView.term) =
  FStarC_Reflection_V2_Builtins.pack_ln
    (FStarC_Reflection_V2_Data.Tv_FVar
       (FStarC_Reflection_V2_Builtins.pack_fv
          ["FStar"; "Pervasives"; "Substitute"]))
let (mk_proj_decl :
  Prims.bool ->
    FStarC_Reflection_Types.name ->
      Prims.string Prims.list ->
        FStar_Tactics_NamedView.univ_name Prims.list ->
          FStar_Tactics_NamedView.binder Prims.list ->
            Prims.nat ->
              FStar_Tactics_NamedView.binder ->
                FStar_Tactics_NamedView.term ->
                  (FStar_Tactics_NamedView.namedv *
                    FStarC_Reflection_Types.fv) Prims.list ->
                    ((FStarC_Reflection_Types.sigelt Prims.list *
                       FStarC_Reflection_Types.fv),
                      unit) FStar_Tactics_Effect.tac_repr)
  =
  fun is_method ->
    fun tyqn ->
      fun ctorname ->
        fun univs ->
          fun params ->
            fun idx ->
              fun field ->
                fun unfold_names_tm ->
                  fun smap ->
                    let uu___ =
                      debug
                        (fun uu___1 ->
                           let uu___2 =
                             FStarC_Tactics_Unseal.unseal
                               field.FStar_Tactics_NamedView.ppname in
                           FStar_Tactics_Effect.tac_bind
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "FStar.Tactics.MkProjectors.fst"
                                      (Prims.of_int (112))
                                      (Prims.of_int (41))
                                      (Prims.of_int (112))
                                      (Prims.of_int (60)))))
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range "Prims.fst"
                                      (Prims.of_int (611))
                                      (Prims.of_int (19))
                                      (Prims.of_int (611))
                                      (Prims.of_int (31)))))
                             (Obj.magic uu___2)
                             (fun uu___3 ->
                                FStar_Tactics_Effect.lift_div_tac
                                  (fun uu___4 ->
                                     Prims.strcat "Processing field " uu___3))) in
                    FStar_Tactics_Effect.tac_bind
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range
                               "FStar.Tactics.MkProjectors.fst"
                               (Prims.of_int (112)) (Prims.of_int (2))
                               (Prims.of_int (112)) (Prims.of_int (61)))))
                      (FStar_Sealed.seal
                         (Obj.magic
                            (FStar_Range.mk_range
                               "FStar.Tactics.MkProjectors.fst"
                               (Prims.of_int (113)) (Prims.of_int (2))
                               (Prims.of_int (198)) (Prims.of_int (35)))))
                      (Obj.magic uu___)
                      (fun uu___1 ->
                         (fun uu___1 ->
                            let uu___2 =
                              debug
                                (fun uu___3 ->
                                   let uu___4 =
                                     FStarC_Tactics_V2_Builtins.term_to_string
                                       field.FStar_Tactics_NamedView.sort in
                                   FStar_Tactics_Effect.tac_bind
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range
                                              "FStar.Tactics.MkProjectors.fst"
                                              (Prims.of_int (113))
                                              (Prims.of_int (36))
                                              (Prims.of_int (113))
                                              (Prims.of_int (61)))))
                                     (FStar_Sealed.seal
                                        (Obj.magic
                                           (FStar_Range.mk_range "Prims.fst"
                                              (Prims.of_int (611))
                                              (Prims.of_int (19))
                                              (Prims.of_int (611))
                                              (Prims.of_int (31)))))
                                     (Obj.magic uu___4)
                                     (fun uu___5 ->
                                        FStar_Tactics_Effect.lift_div_tac
                                          (fun uu___6 ->
                                             Prims.strcat "Field typ = "
                                               uu___5))) in
                            Obj.magic
                              (FStar_Tactics_Effect.tac_bind
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "FStar.Tactics.MkProjectors.fst"
                                          (Prims.of_int (113))
                                          (Prims.of_int (2))
                                          (Prims.of_int (113))
                                          (Prims.of_int (62)))))
                                 (FStar_Sealed.seal
                                    (Obj.magic
                                       (FStar_Range.mk_range
                                          "FStar.Tactics.MkProjectors.fst"
                                          (Prims.of_int (113))
                                          (Prims.of_int (63))
                                          (Prims.of_int (198))
                                          (Prims.of_int (35)))))
                                 (Obj.magic uu___2)
                                 (fun uu___3 ->
                                    (fun uu___3 ->
                                       let uu___4 =
                                         Obj.magic
                                           (FStar_Tactics_Effect.lift_div_tac
                                              (fun uu___5 ->
                                                 FStar_List_Tot_Base.length
                                                   params)) in
                                       Obj.magic
                                         (FStar_Tactics_Effect.tac_bind
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "FStar.Tactics.MkProjectors.fst"
                                                     (Prims.of_int (114))
                                                     (Prims.of_int (11))
                                                     (Prims.of_int (114))
                                                     (Prims.of_int (24)))))
                                            (FStar_Sealed.seal
                                               (Obj.magic
                                                  (FStar_Range.mk_range
                                                     "FStar.Tactics.MkProjectors.fst"
                                                     (Prims.of_int (114))
                                                     (Prims.of_int (27))
                                                     (Prims.of_int (198))
                                                     (Prims.of_int (35)))))
                                            (Obj.magic uu___4)
                                            (fun uu___5 ->
                                               (fun np ->
                                                  let uu___5 =
                                                    Obj.magic
                                                      (FStar_Tactics_Effect.lift_div_tac
                                                         (fun uu___6 ->
                                                            FStarC_Reflection_V2_Builtins.pack_fv
                                                              tyqn)) in
                                                  Obj.magic
                                                    (FStar_Tactics_Effect.tac_bind
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "FStar.Tactics.MkProjectors.fst"
                                                                (Prims.of_int (115))
                                                                (Prims.of_int (13))
                                                                (Prims.of_int (115))
                                                                (Prims.of_int (25)))))
                                                       (FStar_Sealed.seal
                                                          (Obj.magic
                                                             (FStar_Range.mk_range
                                                                "FStar.Tactics.MkProjectors.fst"
                                                                (Prims.of_int (115))
                                                                (Prims.of_int (28))
                                                                (Prims.of_int (198))
                                                                (Prims.of_int (35)))))
                                                       (Obj.magic uu___5)
                                                       (fun uu___6 ->
                                                          (fun tyfv ->
                                                             let uu___6 =
                                                               let uu___7 =
                                                                 FStar_Tactics_V2_Derived.cur_module
                                                                   () in
                                                               FStar_Tactics_Effect.tac_bind
                                                                 (FStar_Sealed.seal
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (116))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (116))
                                                                    (Prims.of_int (31)))))
                                                                 (FStar_Sealed.seal
                                                                    (
                                                                    Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (116))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (116))
                                                                    (Prims.of_int (102)))))
                                                                 (Obj.magic
                                                                    uu___7)
                                                                 (fun uu___8
                                                                    ->
                                                                    (fun
                                                                    uu___8 ->
                                                                    let uu___9
                                                                    =
                                                                    let uu___10
                                                                    =
                                                                    let uu___11
                                                                    =
                                                                    let uu___12
                                                                    =
                                                                    list_last
                                                                    ctorname in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (116))
                                                                    (Prims.of_int (48))
                                                                    (Prims.of_int (116))
                                                                    (Prims.of_int (66)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (116))
                                                                    (Prims.of_int (48))
                                                                    (Prims.of_int (116))
                                                                    (Prims.of_int (101)))))
                                                                    (Obj.magic
                                                                    uu___12)
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    let uu___14
                                                                    =
                                                                    let uu___15
                                                                    =
                                                                    FStarC_Tactics_Unseal.unseal
                                                                    field.FStar_Tactics_NamedView.ppname in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (116))
                                                                    (Prims.of_int (82))
                                                                    (Prims.of_int (116))
                                                                    (Prims.of_int (101)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___15)
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___17
                                                                    ->
                                                                    Prims.strcat
                                                                    "__item__"
                                                                    uu___16)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (116))
                                                                    (Prims.of_int (69))
                                                                    (Prims.of_int (116))
                                                                    (Prims.of_int (101)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___14)
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___16
                                                                    ->
                                                                    Prims.strcat
                                                                    uu___13
                                                                    uu___15))))
                                                                    uu___13) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (116))
                                                                    (Prims.of_int (48))
                                                                    (Prims.of_int (116))
                                                                    (Prims.of_int (101)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___11)
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    Prims.strcat
                                                                    "__proj__"
                                                                    uu___12)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (116))
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (116))
                                                                    (Prims.of_int (101)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (116))
                                                                    (Prims.of_int (34))
                                                                    (Prims.of_int (116))
                                                                    (Prims.of_int (102)))))
                                                                    (Obj.magic
                                                                    uu___10)
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    [uu___11])) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (116))
                                                                    (Prims.of_int (34))
                                                                    (Prims.of_int (116))
                                                                    (Prims.of_int (102)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (116))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (116))
                                                                    (Prims.of_int (102)))))
                                                                    (Obj.magic
                                                                    uu___9)
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    FStar_List_Tot_Base.op_At
                                                                    uu___8
                                                                    uu___10))))
                                                                    uu___8) in
                                                             Obj.magic
                                                               (FStar_Tactics_Effect.tac_bind
                                                                  (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (116))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (116))
                                                                    (Prims.of_int (102)))))
                                                                  (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (116))
                                                                    (Prims.of_int (105))
                                                                    (Prims.of_int (198))
                                                                    (Prims.of_int (35)))))
                                                                  (Obj.magic
                                                                    uu___6)
                                                                  (fun uu___7
                                                                    ->
                                                                    (fun nm
                                                                    ->
                                                                    let uu___7
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___8 ->
                                                                    FStarC_Reflection_V2_Builtins.pack_fv
                                                                    nm)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (117))
                                                                    (Prims.of_int (11))
                                                                    (Prims.of_int (117))
                                                                    (Prims.of_int (21)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (117))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (198))
                                                                    (Prims.of_int (35)))))
                                                                    (Obj.magic
                                                                    uu___7)
                                                                    (fun
                                                                    uu___8 ->
                                                                    (fun fv
                                                                    ->
                                                                    let uu___8
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    FStar_Reflection_V2_Derived.mk_app
                                                                    (FStar_Tactics_NamedView.pack
                                                                    (FStar_Tactics_NamedView.Tv_UInst
                                                                    (tyfv,
                                                                    (FStar_List_Tot_Base.map
                                                                    (fun un
                                                                    ->
                                                                    FStar_Tactics_NamedView.pack_universe
                                                                    (FStar_Tactics_NamedView.Uv_Name
                                                                    un))
                                                                    univs))))
                                                                    (FStar_List_Tot_Base.map
                                                                    binder_argv
                                                                    params))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (118))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (120))
                                                                    (Prims.of_int (47)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (121))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (198))
                                                                    (Prims.of_int (35)))))
                                                                    (Obj.magic
                                                                    uu___8)
                                                                    (fun
                                                                    uu___9 ->
                                                                    (fun rty
                                                                    ->
                                                                    let uu___9
                                                                    =
                                                                    FStar_Tactics_V2_Derived.fresh_binder
                                                                    rty in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (122))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (122))
                                                                    (Prims.of_int (36)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (122))
                                                                    (Prims.of_int (39))
                                                                    (Prims.of_int (198))
                                                                    (Prims.of_int (35)))))
                                                                    (Obj.magic
                                                                    uu___9)
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun rb
                                                                    ->
                                                                    let uu___10
                                                                    =
                                                                    let uu___11
                                                                    =
                                                                    subst_map
                                                                    smap
                                                                    (binder_to_term
                                                                    rb)
                                                                    field.FStar_Tactics_NamedView.sort in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (125))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (125))
                                                                    (Prims.of_int (73)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (125))
                                                                    (Prims.of_int (73)))))
                                                                    (Obj.magic
                                                                    uu___11)
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_V2_SyntaxHelpers.mk_tot_arr
                                                                    (FStar_List_Tot_Base.op_At
                                                                    (FStar_List_Tot_Base.map
                                                                    binder_mk_implicit
                                                                    params)
                                                                    [rb])
                                                                    uu___12))
                                                                    uu___12) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (123))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (125))
                                                                    (Prims.of_int (73)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (127))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (198))
                                                                    (Prims.of_int (35)))))
                                                                    (Obj.magic
                                                                    uu___10)
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    (fun
                                                                    projty ->
                                                                    let uu___11
                                                                    =
                                                                    debug
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    let uu___13
                                                                    =
                                                                    FStarC_Tactics_V2_Builtins.term_to_string
                                                                    projty in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (127))
                                                                    (Prims.of_int (35))
                                                                    (Prims.of_int (127))
                                                                    (Prims.of_int (56)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "Prims.fst"
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (19))
                                                                    (Prims.of_int (611))
                                                                    (Prims.of_int (31)))))
                                                                    (Obj.magic
                                                                    uu___13)
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    Prims.strcat
                                                                    "Proj typ = "
                                                                    uu___14))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (127))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (127))
                                                                    (Prims.of_int (57)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (127))
                                                                    (Prims.of_int (58))
                                                                    (Prims.of_int (198))
                                                                    (Prims.of_int (35)))))
                                                                    (Obj.magic
                                                                    uu___11)
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    let uu___13
                                                                    =
                                                                    FStar_Tactics_NamedView.pack_sigelt
                                                                    (FStar_Tactics_NamedView.Sg_Let
                                                                    {
                                                                    FStar_Tactics_NamedView.isrec
                                                                    = false;
                                                                    FStar_Tactics_NamedView.lbs
                                                                    =
                                                                    [
                                                                    {
                                                                    FStar_Tactics_NamedView.lb_fv
                                                                    = fv;
                                                                    FStar_Tactics_NamedView.lb_us
                                                                    = univs;
                                                                    FStar_Tactics_NamedView.lb_typ
                                                                    = projty;
                                                                    FStar_Tactics_NamedView.lb_def
                                                                    =
                                                                    (FStarC_Reflection_V2_Builtins.pack_ln
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
                                                                    (FStarC_Reflection_V2_Data.Tv_App
                                                                    ((FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_FVar
                                                                    (FStarC_Reflection_V2_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "MkProjectors";
                                                                    "mk_one_projector"]))),
                                                                    (unfold_names_tm,
                                                                    FStarC_Reflection_V2_Data.Q_Explicit)))),
                                                                    ((embed_int
                                                                    np),
                                                                    FStarC_Reflection_V2_Data.Q_Explicit)))),
                                                                    ((embed_int
                                                                    idx),
                                                                    FStarC_Reflection_V2_Data.Q_Explicit))))))),
                                                                    FStarC_Reflection_V2_Data.Q_Explicit))))
                                                                    }]
                                                                    }) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (128))
                                                                    (Prims.of_int (16))
                                                                    (Prims.of_int (142))
                                                                    (Prims.of_int (7)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (143))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (198))
                                                                    (Prims.of_int (35)))))
                                                                    (Obj.magic
                                                                    uu___13)
                                                                    (fun
                                                                    uu___14
                                                                    ->
                                                                    (fun
                                                                    se_proj
                                                                    ->
                                                                    let uu___14
                                                                    =
                                                                    if
                                                                    Prims.op_Negation
                                                                    is_method
                                                                    then
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___15
                                                                    -> [])))
                                                                    else
                                                                    Obj.magic
                                                                    (Obj.repr
                                                                    (if
                                                                    FStar_List_Tot_Base.existsb
                                                                    (FStar_Reflection_TermEq_Simple.term_eq
                                                                    (FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_FVar
                                                                    (FStarC_Reflection_V2_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "Typeclasses";
                                                                    "no_method"]))))
                                                                    field.FStar_Tactics_NamedView.attrs
                                                                    then
                                                                    Obj.repr
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___16
                                                                    -> []))
                                                                    else
                                                                    Obj.repr
                                                                    (let uu___17
                                                                    =
                                                                    let uu___18
                                                                    =
                                                                    let uu___19
                                                                    =
                                                                    FStar_Tactics_V2_Derived.cur_module
                                                                    () in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (147))
                                                                    (Prims.of_int (27))
                                                                    (Prims.of_int (147))
                                                                    (Prims.of_int (40)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (147))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (147))
                                                                    (Prims.of_int (65)))))
                                                                    (Obj.magic
                                                                    uu___19)
                                                                    (fun
                                                                    uu___20
                                                                    ->
                                                                    (fun
                                                                    uu___20
                                                                    ->
                                                                    let uu___21
                                                                    =
                                                                    let uu___22
                                                                    =
                                                                    FStarC_Tactics_Unseal.unseal
                                                                    field.FStar_Tactics_NamedView.ppname in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (147))
                                                                    (Prims.of_int (44))
                                                                    (Prims.of_int (147))
                                                                    (Prims.of_int (63)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (147))
                                                                    (Prims.of_int (43))
                                                                    (Prims.of_int (147))
                                                                    (Prims.of_int (64)))))
                                                                    (Obj.magic
                                                                    uu___22)
                                                                    (fun
                                                                    uu___23
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___24
                                                                    ->
                                                                    [uu___23])) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (147))
                                                                    (Prims.of_int (43))
                                                                    (Prims.of_int (147))
                                                                    (Prims.of_int (64)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (147))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (147))
                                                                    (Prims.of_int (65)))))
                                                                    (Obj.magic
                                                                    uu___21)
                                                                    (fun
                                                                    uu___22
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___23
                                                                    ->
                                                                    FStar_List_Tot_Base.op_At
                                                                    uu___20
                                                                    uu___22))))
                                                                    uu___20) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (147))
                                                                    (Prims.of_int (26))
                                                                    (Prims.of_int (147))
                                                                    (Prims.of_int (65)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (147))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (147))
                                                                    (Prims.of_int (65)))))
                                                                    (Obj.magic
                                                                    uu___18)
                                                                    (fun
                                                                    uu___19
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___20
                                                                    ->
                                                                    FStarC_Reflection_V2_Builtins.pack_fv
                                                                    uu___19)) in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (147))
                                                                    (Prims.of_int (18))
                                                                    (Prims.of_int (147))
                                                                    (Prims.of_int (65)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (147))
                                                                    (Prims.of_int (68))
                                                                    (Prims.of_int (181))
                                                                    (Prims.of_int (8)))))
                                                                    (Obj.magic
                                                                    uu___17)
                                                                    (fun
                                                                    uu___18
                                                                    ->
                                                                    (fun
                                                                    meth_fv
                                                                    ->
                                                                    let uu___18
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___19
                                                                    ->
                                                                    {
                                                                    FStar_Tactics_NamedView.uniq
                                                                    =
                                                                    (rb.FStar_Tactics_NamedView.uniq);
                                                                    FStar_Tactics_NamedView.ppname
                                                                    =
                                                                    (rb.FStar_Tactics_NamedView.ppname);
                                                                    FStar_Tactics_NamedView.sort
                                                                    =
                                                                    (rb.FStar_Tactics_NamedView.sort);
                                                                    FStar_Tactics_NamedView.qual
                                                                    =
                                                                    (FStarC_Reflection_V2_Data.Q_Meta
                                                                    (FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_FVar
                                                                    (FStarC_Reflection_V2_Builtins.pack_fv
                                                                    ["FStar";
                                                                    "Tactics";
                                                                    "Typeclasses";
                                                                    "tcresolve"]))));
                                                                    FStar_Tactics_NamedView.attrs
                                                                    =
                                                                    (rb.FStar_Tactics_NamedView.attrs)
                                                                    })) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (148))
                                                                    (Prims.of_int (15))
                                                                    (Prims.of_int (148))
                                                                    (Prims.of_int (61)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (148))
                                                                    (Prims.of_int (66))
                                                                    (Prims.of_int (181))
                                                                    (Prims.of_int (8)))))
                                                                    (Obj.magic
                                                                    uu___18)
                                                                    (fun
                                                                    uu___19
                                                                    ->
                                                                    (fun rb1
                                                                    ->
                                                                    let uu___19
                                                                    =
                                                                    let uu___20
                                                                    =
                                                                    subst_map
                                                                    smap
                                                                    (binder_to_term
                                                                    rb1)
                                                                    field.FStar_Tactics_NamedView.sort in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (151))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (151))
                                                                    (Prims.of_int (75)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (149))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (151))
                                                                    (Prims.of_int (75)))))
                                                                    (Obj.magic
                                                                    uu___20)
                                                                    (fun
                                                                    uu___21
                                                                    ->
                                                                    (fun
                                                                    uu___21
                                                                    ->
                                                                    Obj.magic
                                                                    (FStar_Tactics_V2_SyntaxHelpers.mk_tot_arr
                                                                    (FStar_List_Tot_Base.op_At
                                                                    (FStar_List_Tot_Base.map
                                                                    binder_mk_implicit
                                                                    params)
                                                                    [rb1])
                                                                    uu___21))
                                                                    uu___21) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (149))
                                                                    (Prims.of_int (17))
                                                                    (Prims.of_int (151))
                                                                    (Prims.of_int (75)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (152))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (181))
                                                                    (Prims.of_int (8)))))
                                                                    (Obj.magic
                                                                    uu___19)
                                                                    (fun
                                                                    uu___20
                                                                    ->
                                                                    (fun
                                                                    projty1
                                                                    ->
                                                                    let uu___20
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___21
                                                                    ->
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
                                                                    "MkProjectors";
                                                                    "mk_one_method"]))),
                                                                    ((embed_string
                                                                    (FStarC_Reflection_V2_Builtins.implode_qn
                                                                    nm)),
                                                                    FStarC_Reflection_V2_Data.Q_Explicit)))),
                                                                    ((embed_int
                                                                    np),
                                                                    FStarC_Reflection_V2_Data.Q_Explicit))))))),
                                                                    FStarC_Reflection_V2_Data.Q_Explicit))))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (155))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (168))
                                                                    (Prims.of_int (41)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (169))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (181))
                                                                    (Prims.of_int (8)))))
                                                                    (Obj.magic
                                                                    uu___20)
                                                                    (fun
                                                                    uu___21
                                                                    ->
                                                                    (fun
                                                                    lb_def ->
                                                                    let uu___21
                                                                    =
                                                                    FStar_Tactics_NamedView.pack_sigelt
                                                                    (FStar_Tactics_NamedView.Sg_Let
                                                                    {
                                                                    FStar_Tactics_NamedView.isrec
                                                                    = false;
                                                                    FStar_Tactics_NamedView.lbs
                                                                    =
                                                                    [
                                                                    {
                                                                    FStar_Tactics_NamedView.lb_fv
                                                                    = meth_fv;
                                                                    FStar_Tactics_NamedView.lb_us
                                                                    = univs;
                                                                    FStar_Tactics_NamedView.lb_typ
                                                                    = projty1;
                                                                    FStar_Tactics_NamedView.lb_def
                                                                    = lb_def
                                                                    }]
                                                                    }) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (172))
                                                                    (Prims.of_int (13))
                                                                    (Prims.of_int (179))
                                                                    (Prims.of_int (9)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (181))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (181))
                                                                    (Prims.of_int (8)))))
                                                                    (Obj.magic
                                                                    uu___21)
                                                                    (fun se
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___22
                                                                    -> [se]))))
                                                                    uu___21)))
                                                                    uu___20)))
                                                                    uu___19)))
                                                                    uu___18)))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (145))
                                                                    (Prims.of_int (4))
                                                                    (Prims.of_int (181))
                                                                    (Prims.of_int (8)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (198))
                                                                    (Prims.of_int (2))
                                                                    (Prims.of_int (198))
                                                                    (Prims.of_int (35)))))
                                                                    (Obj.magic
                                                                    uu___14)
                                                                    (fun
                                                                    maybe_se_method
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    (((
                                                                    FStarC_Reflection_V2_Builtins.set_sigelt_attrs
                                                                    (FStar_List_Tot_Base.op_At
                                                                    (substitute_attr
                                                                    ::
                                                                    (field.FStar_Tactics_NamedView.attrs))
                                                                    (FStarC_Reflection_V2_Builtins.sigelt_attrs
                                                                    se_proj))
                                                                    se_proj)
                                                                    ::
                                                                    maybe_se_method),
                                                                    fv)))))
                                                                    uu___14)))
                                                                    uu___12)))
                                                                    uu___11)))
                                                                    uu___10)))
                                                                    uu___9)))
                                                                    uu___8)))
                                                                    uu___7)))
                                                            uu___6))) uu___5)))
                                      uu___3))) uu___1)
let (mk_projs :
  Prims.bool ->
    Prims.string ->
      (FStarC_Reflection_Types.sigelt Prims.list, unit)
        FStar_Tactics_Effect.tac_repr)
  =
  fun is_class ->
    fun tyname ->
      let uu___ =
        debug
          (fun uu___1 ->
             (fun uu___1 ->
                Obj.magic
                  (FStar_Tactics_Effect.lift_div_tac
                     (fun uu___2 ->
                        Prims.strcat "!! mk_projs tactic called on: " tyname)))
               uu___1) in
      FStar_Tactics_Effect.tac_bind
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.MkProjectors.fst"
                 (Prims.of_int (202)) (Prims.of_int (2)) (Prims.of_int (202))
                 (Prims.of_int (61)))))
        (FStar_Sealed.seal
           (Obj.magic
              (FStar_Range.mk_range "FStar.Tactics.MkProjectors.fst"
                 (Prims.of_int (202)) (Prims.of_int (62))
                 (Prims.of_int (232)) (Prims.of_int (29)))))
        (Obj.magic uu___)
        (fun uu___1 ->
           (fun uu___1 ->
              let uu___2 =
                Obj.magic
                  (FStar_Tactics_Effect.lift_div_tac
                     (fun uu___3 ->
                        FStarC_Reflection_V2_Builtins.explode_qn tyname)) in
              Obj.magic
                (FStar_Tactics_Effect.tac_bind
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range
                            "FStar.Tactics.MkProjectors.fst"
                            (Prims.of_int (203)) (Prims.of_int (13))
                            (Prims.of_int (203)) (Prims.of_int (30)))))
                   (FStar_Sealed.seal
                      (Obj.magic
                         (FStar_Range.mk_range
                            "FStar.Tactics.MkProjectors.fst"
                            (Prims.of_int (204)) (Prims.of_int (2))
                            (Prims.of_int (232)) (Prims.of_int (29)))))
                   (Obj.magic uu___2)
                   (fun uu___3 ->
                      (fun tyqn ->
                         let uu___3 =
                           let uu___4 = FStarC_Tactics_V2_Builtins.top_env () in
                           FStar_Tactics_Effect.tac_bind
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "FStar.Tactics.MkProjectors.fst"
                                      (Prims.of_int (204))
                                      (Prims.of_int (19))
                                      (Prims.of_int (204))
                                      (Prims.of_int (31)))))
                             (FStar_Sealed.seal
                                (Obj.magic
                                   (FStar_Range.mk_range
                                      "FStar.Tactics.MkProjectors.fst"
                                      (Prims.of_int (204)) (Prims.of_int (8))
                                      (Prims.of_int (204))
                                      (Prims.of_int (36)))))
                             (Obj.magic uu___4)
                             (fun uu___5 ->
                                FStar_Tactics_Effect.lift_div_tac
                                  (fun uu___6 ->
                                     FStarC_Reflection_V2_Builtins.lookup_typ
                                       uu___5 tyqn)) in
                         Obj.magic
                           (FStar_Tactics_Effect.tac_bind
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "FStar.Tactics.MkProjectors.fst"
                                       (Prims.of_int (204))
                                       (Prims.of_int (8))
                                       (Prims.of_int (204))
                                       (Prims.of_int (36)))))
                              (FStar_Sealed.seal
                                 (Obj.magic
                                    (FStar_Range.mk_range
                                       "FStar.Tactics.MkProjectors.fst"
                                       (Prims.of_int (204))
                                       (Prims.of_int (2))
                                       (Prims.of_int (232))
                                       (Prims.of_int (29)))))
                              (Obj.magic uu___3)
                              (fun uu___4 ->
                                 (fun uu___4 ->
                                    match uu___4 with
                                    | FStar_Pervasives_Native.None ->
                                        Obj.magic
                                          (Obj.repr
                                             (FStar_Tactics_Effect.raise
                                                NotFound))
                                    | FStar_Pervasives_Native.Some se ->
                                        Obj.magic
                                          (Obj.repr
                                             (let uu___5 =
                                                FStar_Tactics_NamedView.inspect_sigelt
                                                  se in
                                              FStar_Tactics_Effect.tac_bind
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "FStar.Tactics.MkProjectors.fst"
                                                         (Prims.of_int (208))
                                                         (Prims.of_int (10))
                                                         (Prims.of_int (208))
                                                         (Prims.of_int (27)))))
                                                (FStar_Sealed.seal
                                                   (Obj.magic
                                                      (FStar_Range.mk_range
                                                         "FStar.Tactics.MkProjectors.fst"
                                                         (Prims.of_int (208))
                                                         (Prims.of_int (4))
                                                         (Prims.of_int (232))
                                                         (Prims.of_int (29)))))
                                                (Obj.magic uu___5)
                                                (fun uu___6 ->
                                                   (fun uu___6 ->
                                                      match uu___6 with
                                                      | FStar_Tactics_NamedView.Sg_Inductive
                                                          {
                                                            FStar_Tactics_NamedView.nm
                                                              = nm;
                                                            FStar_Tactics_NamedView.univs1
                                                              = univs;
                                                            FStar_Tactics_NamedView.params
                                                              = params;
                                                            FStar_Tactics_NamedView.typ
                                                              = typ;
                                                            FStar_Tactics_NamedView.ctors
                                                              = ctors;_}
                                                          ->
                                                          Obj.magic
                                                            (Obj.repr
                                                               (let uu___7 =
                                                                  if
                                                                    (FStar_List_Tot_Base.length
                                                                    ctors) <>
                                                                    Prims.int_one
                                                                  then
                                                                    Obj.magic
                                                                    (FStar_Tactics_V2_Derived.fail
                                                                    "Expected an inductive with one constructor")
                                                                  else
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___9 ->
                                                                    ())) in
                                                                FStar_Tactics_Effect.tac_bind
                                                                  (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (210))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (211))
                                                                    (Prims.of_int (57)))))
                                                                  (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (211))
                                                                    (Prims.of_int (58))
                                                                    (Prims.of_int (230))
                                                                    (Prims.of_int (11)))))
                                                                  (Obj.magic
                                                                    uu___7)
                                                                  (fun uu___8
                                                                    ->
                                                                    (fun
                                                                    uu___8 ->
                                                                    let uu___9
                                                                    =
                                                                    let uu___10
                                                                    =
                                                                    FStar_Tactics_V2_SyntaxHelpers.collect_arr_bs
                                                                    typ in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (212))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (212))
                                                                    (Prims.of_int (44)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (212))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (212))
                                                                    (Prims.of_int (44)))))
                                                                    (Obj.magic
                                                                    uu___10)
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___12
                                                                    ->
                                                                    FStar_Pervasives_Native.fst
                                                                    uu___11)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (212))
                                                                    (Prims.of_int (20))
                                                                    (Prims.of_int (212))
                                                                    (Prims.of_int (44)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (213))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (230))
                                                                    (Prims.of_int (11)))))
                                                                    (Obj.magic
                                                                    uu___9)
                                                                    (fun
                                                                    uu___10
                                                                    ->
                                                                    (fun
                                                                    indices
                                                                    ->
                                                                    let uu___10
                                                                    =
                                                                    if
                                                                    Prims.uu___is_Cons
                                                                    indices
                                                                    then
                                                                    Obj.magic
                                                                    (FStar_Tactics_V2_Derived.fail
                                                                    "Inductive indices nonempty?")
                                                                    else
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___12
                                                                    -> ())) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (213))
                                                                    (Prims.of_int (6))
                                                                    (Prims.of_int (214))
                                                                    (Prims.of_int (42)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (214))
                                                                    (Prims.of_int (43))
                                                                    (Prims.of_int (230))
                                                                    (Prims.of_int (11)))))
                                                                    (Obj.magic
                                                                    uu___10)
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    (fun
                                                                    uu___11
                                                                    ->
                                                                    let uu___12
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___13
                                                                    -> ctors)) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (215))
                                                                    (Prims.of_int (33))
                                                                    (Prims.of_int (215))
                                                                    (Prims.of_int (38)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (214))
                                                                    (Prims.of_int (43))
                                                                    (Prims.of_int (230))
                                                                    (Prims.of_int (11)))))
                                                                    (Obj.magic
                                                                    uu___12)
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    (fun
                                                                    uu___13
                                                                    ->
                                                                    match uu___13
                                                                    with
                                                                    | 
                                                                    (ctorname,
                                                                    ctor_t)::[]
                                                                    ->
                                                                    let uu___14
                                                                    =
                                                                    FStar_Tactics_V2_SyntaxHelpers.collect_arr_bs
                                                                    ctor_t in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (218))
                                                                    (Prims.of_int (24))
                                                                    (Prims.of_int (218))
                                                                    (Prims.of_int (45)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (215))
                                                                    (Prims.of_int (41))
                                                                    (Prims.of_int (230))
                                                                    (Prims.of_int (11)))))
                                                                    (Obj.magic
                                                                    uu___14)
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    (fun
                                                                    uu___15
                                                                    ->
                                                                    match uu___15
                                                                    with
                                                                    | 
                                                                    (fields,
                                                                    uu___16)
                                                                    ->
                                                                    let uu___17
                                                                    =
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___18
                                                                    ->
                                                                    FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_App
                                                                    ((FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_UInst
                                                                    ((FStarC_Reflection_V2_Builtins.pack_fv
                                                                    ["Prims";
                                                                    "Nil"]),
                                                                    [
                                                                    FStarC_Reflection_V2_Builtins.pack_universe
                                                                    FStarC_Reflection_V2_Data.Uv_Zero]))),
                                                                    ((FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_FVar
                                                                    (FStarC_Reflection_V2_Builtins.pack_fv
                                                                    ["Prims";
                                                                    "string"]))),
                                                                    FStarC_Reflection_V2_Data.Q_Implicit))))) in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (219))
                                                                    (Prims.of_int (28))
                                                                    (Prims.of_int (219))
                                                                    (Prims.of_int (46)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (219))
                                                                    (Prims.of_int (49))
                                                                    (Prims.of_int (230))
                                                                    (Prims.of_int (11)))))
                                                                    (Obj.magic
                                                                    uu___17)
                                                                    (fun
                                                                    uu___18
                                                                    ->
                                                                    (fun
                                                                    unfold_names_tm
                                                                    ->
                                                                    let uu___18
                                                                    =
                                                                    FStar_Tactics_Util.fold_left
                                                                    (fun
                                                                    uu___19
                                                                    ->
                                                                    fun field
                                                                    ->
                                                                    match uu___19
                                                                    with
                                                                    | 
                                                                    (decls,
                                                                    smap,
                                                                    unfold_names_tm1,
                                                                    idx) ->
                                                                    let uu___20
                                                                    =
                                                                    mk_proj_decl
                                                                    is_class
                                                                    tyqn
                                                                    ctorname
                                                                    univs
                                                                    params
                                                                    idx field
                                                                    unfold_names_tm1
                                                                    smap in
                                                                    FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (222))
                                                                    (Prims.of_int (25))
                                                                    (Prims.of_int (222))
                                                                    (Prims.of_int (104)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (221))
                                                                    (Prims.of_int (78))
                                                                    (Prims.of_int (226))
                                                                    (Prims.of_int (17)))))
                                                                    (Obj.magic
                                                                    uu___20)
                                                                    (fun
                                                                    uu___21
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___22
                                                                    ->
                                                                    match uu___21
                                                                    with
                                                                    | 
                                                                    (ds, fv)
                                                                    ->
                                                                    ((FStar_List_Tot_Base.op_At
                                                                    decls ds),
                                                                    (((FStar_Tactics_V2_SyntaxCoercions.binder_to_namedv
                                                                    field),
                                                                    fv) ::
                                                                    smap),
                                                                    (FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_App
                                                                    ((FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_App
                                                                    ((FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_App
                                                                    ((FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_UInst
                                                                    ((FStarC_Reflection_V2_Builtins.pack_fv
                                                                    ["Prims";
                                                                    "Cons"]),
                                                                    [
                                                                    FStarC_Reflection_V2_Builtins.pack_universe
                                                                    FStarC_Reflection_V2_Data.Uv_Zero]))),
                                                                    ((FStarC_Reflection_V2_Builtins.pack_ln
                                                                    (FStarC_Reflection_V2_Data.Tv_FVar
                                                                    (FStarC_Reflection_V2_Builtins.pack_fv
                                                                    ["Prims";
                                                                    "string"]))),
                                                                    FStarC_Reflection_V2_Data.Q_Implicit)))),
                                                                    ((embed_string
                                                                    (FStarC_Reflection_V2_Builtins.implode_qn
                                                                    (FStarC_Reflection_V2_Builtins.inspect_fv
                                                                    fv))),
                                                                    FStarC_Reflection_V2_Data.Q_Explicit)))),
                                                                    (unfold_names_tm1,
                                                                    FStarC_Reflection_V2_Data.Q_Explicit)))),
                                                                    (idx +
                                                                    Prims.int_one)))))
                                                                    ([], [],
                                                                    unfold_names_tm,
                                                                    Prims.int_zero)
                                                                    fields in
                                                                    Obj.magic
                                                                    (FStar_Tactics_Effect.tac_bind
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (221))
                                                                    (Prims.of_int (8))
                                                                    (Prims.of_int (228))
                                                                    (Prims.of_int (14)))))
                                                                    (FStar_Sealed.seal
                                                                    (Obj.magic
                                                                    (FStar_Range.mk_range
                                                                    "FStar.Tactics.MkProjectors.fst"
                                                                    (Prims.of_int (219))
                                                                    (Prims.of_int (49))
                                                                    (Prims.of_int (230))
                                                                    (Prims.of_int (11)))))
                                                                    (Obj.magic
                                                                    uu___18)
                                                                    (fun
                                                                    uu___19
                                                                    ->
                                                                    FStar_Tactics_Effect.lift_div_tac
                                                                    (fun
                                                                    uu___20
                                                                    ->
                                                                    match uu___19
                                                                    with
                                                                    | 
                                                                    (decls,
                                                                    uu___21,
                                                                    uu___22,
                                                                    uu___23)
                                                                    -> decls))))
                                                                    uu___18)))
                                                                    uu___15)))
                                                                    uu___13)))
                                                                    uu___11)))
                                                                    uu___10)))
                                                                    uu___8)))
                                                      | uu___7 ->
                                                          Obj.magic
                                                            (Obj.repr
                                                               (FStar_Tactics_V2_Derived.fail
                                                                  "not an inductive")))
                                                     uu___6)))) uu___4)))
                        uu___3))) uu___1)
let _ =
  FStarC_Tactics_Native.register_tactic "FStar.Tactics.MkProjectors.mk_projs"
    (Prims.of_int (3))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             FStarC_Tactics_InterpFuns.mk_tactic_interpretation_2
               "FStar.Tactics.MkProjectors.mk_projs (plugin)"
               (FStarC_Tactics_Native.from_tactic_2 mk_projs)
               FStarC_Syntax_Embeddings.e_bool
               FStarC_Syntax_Embeddings.e_string
               (FStarC_Syntax_Embeddings.e_list
                  FStarC_Reflection_V2_Embeddings.e_sigelt) psc ncb us args)