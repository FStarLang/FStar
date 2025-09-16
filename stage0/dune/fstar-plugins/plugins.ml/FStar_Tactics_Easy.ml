open Fstarcompiler
open Prims
let (easy_fill : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    let uu___1 =
      FStar_Tactics_V2_Derived.repeat FStarC_Tactics_V2_Builtins.intro in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.Easy.fst"
               (Prims.of_int (22)) (Prims.of_int (12)) (Prims.of_int (22))
               (Prims.of_int (24)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.Easy.fst"
               (Prims.of_int (22)) (Prims.of_int (27)) (Prims.of_int (25))
               (Prims.of_int (10))))) (Obj.magic uu___1)
      (fun uu___2 ->
         (fun uu___2 ->
            let uu___3 =
              FStar_Tactics_V2_Derived.trytac
                (fun uu___4 ->
                   let uu___5 =
                     FStar_Tactics_V2_Derived.apply
                       (FStarC_Reflection_V2_Builtins.pack_ln
                          (FStarC_Reflection_V2_Data.Tv_FVar
                             (FStarC_Reflection_V2_Builtins.pack_fv
                                ["FStar";
                                "Tactics";
                                "Logic";
                                "Lemmas";
                                "lemma_from_squash"]))) in
                   FStar_Tactics_Effect.tac_bind
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "FStar.Tactics.Easy.fst"
                              (Prims.of_int (24)) (Prims.of_int (30))
                              (Prims.of_int (24)) (Prims.of_int (56)))))
                     (FStar_Sealed.seal
                        (Obj.magic
                           (FStar_Range.mk_range "FStar.Tactics.Easy.fst"
                              (Prims.of_int (24)) (Prims.of_int (58))
                              (Prims.of_int (24)) (Prims.of_int (66)))))
                     (Obj.magic uu___5)
                     (fun uu___6 ->
                        (fun uu___6 ->
                           Obj.magic (FStarC_Tactics_V2_Builtins.intro ()))
                          uu___6)) in
            Obj.magic
              (FStar_Tactics_Effect.tac_bind
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "FStar.Tactics.Easy.fst"
                          (Prims.of_int (24)) (Prims.of_int (12))
                          (Prims.of_int (24)) (Prims.of_int (67)))))
                 (FStar_Sealed.seal
                    (Obj.magic
                       (FStar_Range.mk_range "FStar.Tactics.Easy.fst"
                          (Prims.of_int (25)) (Prims.of_int (4))
                          (Prims.of_int (25)) (Prims.of_int (10)))))
                 (Obj.magic uu___3)
                 (fun uu___4 ->
                    (fun uu___4 ->
                       Obj.magic (FStar_Tactics_V2_Derived.smt ())) uu___4)))
           uu___2)
let _ =
  Fstarcompiler.FStarC_Tactics_Native.register_tactic
    "FStar.Tactics.Easy.easy_fill" (Prims.of_int (2))
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             Fstarcompiler.FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.Easy.easy_fill (plugin)"
               (Fstarcompiler.FStarC_Tactics_Native.from_tactic_1 easy_fill)
               Fstarcompiler.FStarC_Syntax_Embeddings.e_unit
               Fstarcompiler.FStarC_Syntax_Embeddings.e_unit psc ncb us args)
let easy : 'a . 'a -> 'a = fun x -> x
