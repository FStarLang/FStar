open Prims
type 'a __result =
  | Success of ('a * FStar_Tactics_Types.proofstate) 
  | Failed of (Prims.exn * FStar_Tactics_Types.proofstate) 
let uu___is_Success : 'a . 'a __result -> Prims.bool =
  fun projectee  ->
    match projectee with | Success _0 -> true | uu____60056 -> false
  
let __proj__Success__item___0 :
  'a . 'a __result -> ('a * FStar_Tactics_Types.proofstate) =
  fun projectee  -> match projectee with | Success _0 -> _0 
let uu___is_Failed : 'a . 'a __result -> Prims.bool =
  fun projectee  ->
    match projectee with | Failed _0 -> true | uu____60106 -> false
  
let __proj__Failed__item___0 :
  'a . 'a __result -> (Prims.exn * FStar_Tactics_Types.proofstate) =
  fun projectee  -> match projectee with | Failed _0 -> _0 