exception UnsupportedJson

type json =
| JsonNull
| JsonBool of bool
| JsonInt of Z.t
| JsonStr of string
| JsonList of json list
| JsonAssoc of (string * json) list

let json_of_yojson yjs: json option =
  let rec aux yjs =
    match yjs with
    | `Null -> JsonNull
    | `Bool b -> JsonBool b
    | `Int i -> JsonInt (Z.of_int i)
    | `String s -> JsonStr s
    | `List l -> JsonList (List.map aux l)
    | `Assoc a -> JsonAssoc (List.map (fun (k, v) -> (k, aux v)) a)
    | _ -> raise UnsupportedJson in
  try Some (aux yjs) with UnsupportedJson -> None

let rec yojson_of_json js =
  match js with
  | JsonNull -> `Null
  | JsonBool b -> `Bool b
  | JsonInt i -> `Int (Z.to_int i)
  | JsonStr s -> `String s
  | JsonList l -> `List (List.map yojson_of_json l)
  | JsonAssoc a -> `Assoc (List.map (fun (k, v) -> (k, yojson_of_json v)) a)

let json_of_string str : json option =
  let open Yojson.Basic in
  try
    json_of_yojson (Yojson.Basic.from_string str)
  with Yojson.Json_error _ -> None

let string_of_json json =
  Yojson.Basic.to_string (yojson_of_json json)
