open Prims
type 'a __result =
  | Success of ('a * FStarC_Tactics_Types.proofstate) 
let uu___is_Success (projectee : 'a __result) : Prims.bool= true
let __proj__Success__item___0 (projectee : 'a __result) :
  ('a * FStarC_Tactics_Types.proofstate)=
  match projectee with | Success _0 -> _0
type proofstate = FStarC_Tactics_Types.proofstate
