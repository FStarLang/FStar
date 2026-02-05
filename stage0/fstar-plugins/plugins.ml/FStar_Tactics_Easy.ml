open Fstarcompiler
open Prims
let easy_fill (uu___ : unit) : (unit, unit) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    let x =
      FStar_Tactics_V2_Derived.repeat FStarC_Tactics_V2_Builtins.intro ps in
    let x1 =
      FStar_Tactics_V2_Derived.trytac
        (fun uu___1 ps1 ->
           FStar_Tactics_V2_Derived.apply
             (FStarC_Reflection_V2_Builtins.pack_ln
                (FStarC_Reflection_V2_Data.Tv_FVar
                   (FStarC_Reflection_V2_Builtins.pack_fv
                      ["FStar";
                      "Tactics";
                      "Logic";
                      "Lemmas";
                      "lemma_from_squash"]))) ps1;
           FStarC_Tactics_V2_Builtins.intro () ps1) ps in
    FStar_Tactics_V2_Derived.smt () ps
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
let easy (x : 'a) : 'a= x
