open Prims
type 'a __result =
  | Success of ('a,FStar_Tactics_Types.proofstate)
  FStar_Pervasives_Native.tuple2 
  | Failed of (Prims.exn,FStar_Tactics_Types.proofstate)
  FStar_Pervasives_Native.tuple2 
let uu___is_Success : 'a . 'a __result -> Prims.bool =
  fun projectee  ->
    match projectee with | Success _0 -> true | uu____47 -> false
  
let __proj__Success__item___0 :
  'a .
    'a __result ->
      ('a,FStar_Tactics_Types.proofstate) FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Success _0 -> _0 
let uu___is_Failed : 'a . 'a __result -> Prims.bool =
  fun projectee  ->
    match projectee with | Failed _0 -> true | uu____98 -> false
  
let __proj__Failed__item___0 :
  'a .
    'a __result ->
      (Prims.exn,FStar_Tactics_Types.proofstate)
        FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Failed _0 -> _0 