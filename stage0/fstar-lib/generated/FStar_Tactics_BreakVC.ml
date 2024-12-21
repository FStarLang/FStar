open Prims
type ('ps, 'p) break_wp' = unit FStar_Pervasives.spinoff
let (post : unit -> (unit, unit) FStar_Tactics_Effect.tac_repr) =
  fun uu___ ->
    let uu___1 =
      FStarC_Tactics_V2_Builtins.norm
        [FStar_Pervasives.delta_fully
           ["FStar.Tactics.BreakVC.mono_lem";
           "FStar.Tactics.BreakVC.break_wp'"]] in
    FStar_Tactics_Effect.tac_bind
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.BreakVC.fsti"
               (Prims.of_int (13)) (Prims.of_int (2)) (Prims.of_int (13))
               (Prims.of_int (46)))))
      (FStar_Sealed.seal
         (Obj.magic
            (FStar_Range.mk_range "FStar.Tactics.BreakVC.fsti"
               (Prims.of_int (14)) (Prims.of_int (2)) (Prims.of_int (14))
               (Prims.of_int (9))))) (Obj.magic uu___1)
      (fun uu___2 ->
         (fun uu___2 -> Obj.magic (FStar_Tactics_V2_Derived.trefl ())) uu___2)
type ('ps, 'p) break_wp = unit FStar_Pervasives.spinoff
type ('p, 'q) op_Equals_Equals_Greater_Greater = unit
let (break_vc :
  unit -> (unit, unit FStar_Pervasives.spinoff) FStar_Tactics_Effect.tac_repr)
  =
  fun uu___ ->
    (fun uu___ ->
       Obj.magic (FStar_Tactics_Effect.lift_div_tac (fun uu___1 -> ())))
      uu___