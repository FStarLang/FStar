open Prims
let bool_of_string (s : Prims.string) :
  Prims.bool FStar_Pervasives_Native.option =
  match s with
  | "true" -> Some true
  | "false" -> Some false
  | _ -> None

let int_of_string (s : Prims.string) :
  Prims.int FStar_Pervasives_Native.option =
  if String.length s = 0 then None
  else try Some (Z.of_string s)
  with Invalid_argument _ -> None
