(*
   Copyright 2017-2024 Microsoft Research

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
module FStarC.Real

module BU = FStarC.Util

let rec dropWhile f xs =
  match xs with
  | [] -> []
  | x::xs ->
    if f x
    then dropWhile f xs
    else x::xs

let int_frac (r : real): option (string & string) =
  match String.split ['.'] r._0 with
  | [i; f] ->
    let i = String.list_of_string i in
    let f = String.list_of_string f in
    let i = i |> dropWhile (fun c -> c = '0') in
    let f = f |> List.rev |> dropWhile (fun c -> c = '0') |> List.rev in
    Some (String.string_of_list i, String.string_of_list f)
  | _ -> None

let max x y =
  if x > y then x else y

let zeropad_match (f1 : string) (f2 : string): string & string =
  let len = max (String.length f1) (String.length f2) in
  let f1 = f1 ^ String.make (len - String.length f1) '0' in
  let f2 = f2 ^ String.make (len - String.length f2) '0' in
  f1, f2

let cmp (r1 r2 : real) : option order =
  match int_frac r1, int_frac r2 with
  | Some (i1, f1), Some (i2, f2) ->
    let f1, f2 = zeropad_match f1 f2 in
    let i1 = BU.int_of_string i1 in
    let i2 = BU.int_of_string i2 in
    let f1 = BU.int_of_string f1 in
    let f2 = BU.int_of_string f2 in
    Some <| FStarC.Class.Ord.cmp (i1, f1) (i2, f2) // lex order

  | _ ->
    None
