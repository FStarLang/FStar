open Prims
let easy_fill (uu___ : unit) (ps : FStarC_Tactics_Types.ref_proofstate) :
  unit=
  let x = FStar_Tactics_V2_Derived.repeat FStarC_Tactics_V2_Builtins.intro ps in
  FStar_Tactics_V2_Derived.smt () ps
let _ =
  FStarC_Tactics_Native.register_tactic "FStar.Tactics.Easy.easy_fill"
    (Prims.of_int 2)
    (fun psc ->
       fun ncb ->
         fun us ->
           fun args ->
             FStarC_Tactics_InterpFuns.mk_tactic_interpretation_1
               "FStar.Tactics.Easy.easy_fill (plugin)"
               (FStarC_Tactics_Native.from_tactic_1 easy_fill)
               FStarC_Syntax_Embeddings.e_unit
               FStarC_Syntax_Embeddings.e_unit psc ncb us args)
let easy (x : 'a) : 'a= x
