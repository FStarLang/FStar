open Prims
type 'a tac_repr = FStarC_Tactics_Types.ref_proofstate -> 'a
let tac_return (x : 'a) (uu___ : FStarC_Tactics_Types.ref_proofstate) : 'a= x
let tac_bind (t1 : FStarC_Tactics_Types.ref_proofstate -> 'a)
  (t2 : 'a -> FStarC_Tactics_Types.ref_proofstate -> 'b)
  (ps : FStarC_Tactics_Types.ref_proofstate) : 'b= let x = t1 ps in t2 x ps
let lift_div_tac (f : unit -> 'a)
  (uu___ : FStarC_Tactics_Types.ref_proofstate) : 'a= f ()
let rewrite_with_tactic
  (uu___ : unit -> FStarC_Tactics_Types.ref_proofstate -> unit)
  (uu___1 : unit) (p : Obj.t) : Obj.t= p
let synth_by_tactic
  (uu___ : unit -> FStarC_Tactics_Types.ref_proofstate -> unit) : 'uuuuu=
  Prims.admit ()
let assume_safe (tau : unit -> FStarC_Tactics_Types.ref_proofstate -> 'a) :
  FStarC_Tactics_Types.ref_proofstate -> 'a= tau ()
type ('a, 'b) tac = 'a -> FStarC_Tactics_Types.ref_proofstate -> 'b
type 'a tactic = (unit, 'a) tac
