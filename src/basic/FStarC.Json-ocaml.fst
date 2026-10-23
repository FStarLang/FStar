(*
   Copyright 2008-2026 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
module FStarC.Json

open FStarC.Effect

[@@custard_extern "Yojson.Basic.t"]
private assume new type yojson : Type0

(* 0 null, 1 bool, 2 int, 3 string, 4 list, 5 assoc, 6 anything else *)
[@@custard_extern "(function `Null -> Z.zero | `Bool _ -> Z.one | `Int _ -> Z.of_int 2 | `String _ -> Z.of_int 3 | `List _ -> Z.of_int 4 | `Assoc _ -> Z.of_int 5 | _ -> Z.of_int 6)"]
private assume val tag : yojson -> int

[@@custard_extern "(function `Bool b -> b | _ -> assert false)"]
private assume val get_bool : yojson -> bool

[@@custard_extern "(function `Int i -> Z.of_int i | _ -> assert false)"]
private assume val get_int : yojson -> int

[@@custard_extern "(function `String s -> s | _ -> assert false)"]
private assume val get_string : yojson -> string

[@@custard_extern "(function `List l -> l | _ -> assert false)"]
private assume val get_list : j:yojson -> l:list yojson{l << j}

[@@custard_extern "(function `Assoc l -> l | _ -> assert false)"]
private assume val get_assoc : j:yojson -> l:list (string & yojson){l << j}

[@@custard_extern "(`Null : Yojson.Basic.t)"]
private assume val mk_null : yojson

[@@custard_extern "(fun b -> (`Bool b : Yojson.Basic.t))"]
private assume val mk_bool : bool -> yojson

[@@custard_extern "(fun i -> (`Int (Z.to_int i) : Yojson.Basic.t))"]
private assume val mk_int : int -> yojson

[@@custard_extern "(fun s -> (`String s : Yojson.Basic.t))"]
private assume val mk_string : string -> yojson

[@@custard_extern "(fun l -> (`List l : Yojson.Basic.t))"]
private assume val mk_list : list yojson -> yojson

[@@custard_extern "(fun l -> (`Assoc l : Yojson.Basic.t))"]
private assume val mk_assoc : list (string & yojson) -> yojson

[@@custard_extern "(fun s -> try Some (Yojson.Basic.from_string s) with Yojson.Json_error _ -> None)"]
private assume val parse : string -> option yojson

[@@custard_extern "(fun j -> Yojson.Basic.to_string j)"]
private assume val print : yojson -> string

let rec json_of_yojson (j : yojson) : option json =
  match tag j with
  | 0 -> Some JsonNull
  | 1 -> Some (JsonBool (get_bool j))
  | 2 -> Some (JsonInt (get_int j))
  | 3 -> Some (JsonStr (get_string j))
  | 4 -> (match json_of_yojson_list (get_list j) with
          | Some l -> Some (JsonList l)
          | None -> None)
  | 5 -> (match json_of_yojson_assoc (get_assoc j) with
          | Some l -> Some (JsonAssoc l)
          | None -> None)
  | _ -> None
and json_of_yojson_list (l : list yojson) : option (list json) =
  match l with
  | [] -> Some []
  | x :: xs ->
    (match json_of_yojson x, json_of_yojson_list xs with
     | Some x, Some xs -> Some (x :: xs)
     | _ -> None)
and json_of_yojson_assoc (l : list (string & yojson)) : option (list (string & json)) =
  match l with
  | [] -> Some []
  | (k, v) :: xs ->
    (match json_of_yojson v, json_of_yojson_assoc xs with
     | Some v, Some xs -> Some ((k, v) :: xs)
     | _ -> None)

let rec yojson_of_json (j : json) : yojson =
  match j with
  | JsonNull -> mk_null
  | JsonBool b -> mk_bool b
  | JsonInt i -> mk_int i
  | JsonStr s -> mk_string s
  | JsonList l -> mk_list (yojson_of_list l)
  | JsonAssoc a -> mk_assoc (yojson_of_assoc a)
and yojson_of_list (l : list json) : list yojson =
  match l with
  | [] -> []
  | x :: xs -> yojson_of_json x :: yojson_of_list xs
and yojson_of_assoc (a : list (string & json)) : list (string & yojson) =
  match a with
  | [] -> []
  | (k, v) :: xs -> (k, yojson_of_json v) :: yojson_of_assoc xs

let json_of_string str =
  match parse str with
  | None -> None
  | Some j -> json_of_yojson j

let string_of_json json = print (yojson_of_json json)
