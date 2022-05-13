open Prims
type 'a __result =
  | Success of ('a * FStar_Tactics_Types.proofstate) 
  | Failed of (Prims.exn * FStar_Tactics_Types.proofstate) 
let uu___is_Success : 'a . 'a __result -> Prims.bool =
  fun projectee -> match projectee with | Success _0 -> true | uu___ -> false
let __proj__Success__item___0 :
  'a . 'a __result -> ('a * FStar_Tactics_Types.proofstate) =
  fun projectee -> match projectee with | Success _0 -> _0
let uu___is_Failed : 'a . 'a __result -> Prims.bool =
  fun projectee -> match projectee with | Failed _0 -> true | uu___ -> false
let __proj__Failed__item___0 :
  'a . 'a __result -> (Prims.exn * FStar_Tactics_Types.proofstate) =
  fun projectee -> match projectee with | Failed _0 -> _0
type 'a tc_result =
  | Tc_success of 'a 
  | Tc_failure of Prims.string 
let uu___is_Tc_success : 'a . 'a tc_result -> Prims.bool =
  fun projectee ->
    match projectee with | Tc_success _0 -> true | uu___ -> false
let __proj__Tc_success__item___0 : 'a . 'a tc_result -> 'a =
  fun projectee -> match projectee with | Tc_success _0 -> _0
let uu___is_Tc_failure : 'a . 'a tc_result -> Prims.bool =
  fun projectee ->
    match projectee with | Tc_failure _0 -> true | uu___ -> false
let __proj__Tc_failure__item___0 : 'a . 'a tc_result -> Prims.string =
  fun projectee -> match projectee with | Tc_failure _0 -> _0