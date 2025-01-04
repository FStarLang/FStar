open Prims
type 'dummyV0 type_powerset =
  | Mk of (unit -> Prims.bool) 
let (uu___is_Mk : (unit -> Prims.bool) -> unit type_powerset -> Prims.bool) =
  fun uu___ -> fun projectee -> true
let (__proj__Mk__item__f :
  (unit -> Prims.bool) -> unit type_powerset -> unit -> Prims.bool) =
  fun uu___ -> fun projectee -> match projectee with | Mk f -> f