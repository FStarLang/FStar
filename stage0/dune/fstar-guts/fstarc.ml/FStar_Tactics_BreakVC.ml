open Prims

let post (uu___ : unit) : (unit, Obj.t) FStar_Tactics_Effect.tac_repr=
  fun ps ->
    FStarC_Tactics_V2_Builtins.norm
      [FStarC_NormSteps.delta_fully
         ["FStar.Tactics.BreakVC.mono_lem";
         "FStar.Tactics.BreakVC.break_wp'"]] ps;
    FStar_Tactics_V2_Derived.trefl () ps

let break_vc (uu___ : unit) : (unit, Obj.t) FStar_Tactics_Effect.tac_repr=
  fun uu___1 -> ()
