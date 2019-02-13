
open Prims
open FStar_Pervasives
type 'a __result =
| Success of ('a * FStar_Tactics_Types.proofstate)
| Failed of (Prims.exn * FStar_Tactics_Types.proofstate)


let uu___is_Success : 'a . 'a __result  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Success (_0) -> begin
true
end
| uu____47 -> begin
false
end))


let __proj__Success__item___0 : 'a . 'a __result  ->  ('a * FStar_Tactics_Types.proofstate) = (fun projectee -> (match (projectee) with
| Success (_0) -> begin
_0
end))


let uu___is_Failed : 'a . 'a __result  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Failed (_0) -> begin
true
end
| uu____98 -> begin
false
end))


let __proj__Failed__item___0 : 'a . 'a __result  ->  (Prims.exn * FStar_Tactics_Types.proofstate) = (fun projectee -> (match (projectee) with
| Failed (_0) -> begin
_0
end))




