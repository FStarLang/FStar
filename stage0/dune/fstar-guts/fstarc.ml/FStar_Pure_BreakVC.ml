open Prims

let post (uu___ : unit) : (unit, Obj.t) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    FStarC_Tactics_V2_Builtins.norm
      [FStarC_NormSteps.delta_fully
         ["FStar.Pure.BreakVC.mono_lem"; "FStar.Pure.BreakVC.break_wp'"]] ps;
    FStar_Tactics_V2_Derived.trefl () ps

