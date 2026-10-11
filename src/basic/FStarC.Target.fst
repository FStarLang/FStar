(*
   Copyright 2026 Microsoft Research

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
module FStarC.Target

open FStarC
open FStarC.Effect
open FStarC.List

let is_target_name (s:string) : ML bool =
  match String.list_of_string s with
  | c :: cs ->
    let is_lower c = Util.is_letter c && String.lowercase (String.string_of_char c) = String.string_of_char c in
    is_lower c && List.for_all (fun c -> is_lower c || Util.is_digit c || c = '_') cs
  | [] -> false

let split_target (stem:string) : ML (string & option string) =
  match List.rev (String.split ['-'] stem) with
  | t :: rest when Cons? rest && is_target_name t ->
    String.concat "-" (List.rev rest), Some t
  | _ -> stem, None
