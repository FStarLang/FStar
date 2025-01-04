open Prims
type 'a __result =
  | Success of ('a * FStarC_Tactics_Types.proofstate) 
  | Failed of (Prims.exn * FStarC_Tactics_Types.proofstate) 
let uu___is_Success : 'a . 'a __result -> Prims.bool =
  fun projectee -> match projectee with | Success _0 -> true | uu___ -> false
let __proj__Success__item___0 :
  'a . 'a __result -> ('a * FStarC_Tactics_Types.proofstate) =
  fun projectee -> match projectee with | Success _0 -> _0
let uu___is_Failed : 'a . 'a __result -> Prims.bool =
  fun projectee -> match projectee with | Failed _0 -> true | uu___ -> false
let __proj__Failed__item___0 :
  'a . 'a __result -> (Prims.exn * FStarC_Tactics_Types.proofstate) =
  fun projectee -> match projectee with | Failed _0 -> _0
type proofstate = FStarC_Tactics_Types.proofstate