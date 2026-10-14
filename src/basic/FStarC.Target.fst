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

let is_segment (s:string) : ML bool =
  match String.list_of_string s with
  | c :: cs ->
    let is_lower c = Util.is_letter c && String.lowercase (String.string_of_char c) = String.string_of_char c in
    is_lower c && List.for_all (fun c -> is_lower c || Util.is_digit c || c = '_') cs
  | [] -> false

let is_atom (a:string) : ML bool =
  List.for_all is_segment (String.split ['.'] a)

(* [a] is [b] or one of its ancestors. *)
let atom_implied_by (a b:string) : ML bool =
  a = b || Util.starts_with b (a ^ ".")

let atoms (t:tag) : ML (list string) =
  match t with
  | None -> []
  | Some s -> String.split ['-'] s

let canonical (xs:list string) : ML tag =
  let xs = xs |> List.filter (fun a ->
    not (List.existsb (fun b -> b <> a && atom_implied_by a b) xs)) in
  match Util.sort_with String.compare (List.deduplicate (fun a b -> a = b) xs) with
  | [] -> None
  | xs -> Some (String.concat "-" xs)

let parse_tag (s:string) : ML (option tag) =
  let xs = String.split ['-'] s in
  if List.for_all is_atom xs then Some (canonical xs) else None

let split_target (stem:string) : ML (string & tag) =
  match String.split ['-'] stem with
  | m :: rest when Cons? rest ->
    (match parse_tag (String.concat "-" rest) with
     | Some t -> m, t
     | None -> stem, None)
  | _ -> stem, None

let join (t1 t2:tag) : ML tag = canonical (atoms t1 @ atoms t2)

let implies (ctx t:tag) : ML bool =
  let cs = atoms ctx in
  List.for_all (fun a -> List.existsb (atom_implied_by a) cs) (atoms t)

let diverge (a b:string) : ML bool =
  match String.split ['.'] a, String.split ['.'] b with
  | x :: _, y :: _ -> x = y && not (atom_implied_by a b) && not (atom_implied_by b a)
  | _ -> false

let compatible (t1 t2:tag) : ML bool =
  let bs = atoms t2 in
  List.for_all (fun a -> not (List.existsb (diverge a) bs)) (atoms t1)

let prefixes (a:string) : ML (list string) =
  let rec go (acc:list string) (cur:string) (segs:list string) : ML (list string) =
    match segs with
    | [] -> acc
    | s :: rest ->
      let cur = if cur = "" then s else cur ^ "." ^ s in
      go (cur :: acc) cur rest
  in
  go [] "" (String.split ['.'] a)

let applicable_tags (ctx:tag) : ML (list tag) =
  let closure = List.deduplicate (fun a b -> a = b) (List.collect prefixes (atoms ctx)) in
  let rec subsets (xs:list string) : ML (list (list string)) =
    match xs with
    | [] -> [[]]
    | x :: xs -> let s = subsets xs in List.map (fun l -> x :: l) s @ s
  in
  let tags = List.deduplicate (fun a b -> a = b) (List.map canonical (subsets closure)) in
  Util.sort_with (fun a b -> List.length (atoms b) - List.length (atoms a)) tags

let show_tag (t:tag) : string =
  match t with
  | None -> "(common)"
  | Some s -> s
