﻿(*
   Copyright 2008-2024 Microsoft Research

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
module FStarC.Options.Ext

open FStarC
open FStarC.Effect
open FStarC.Class.Show
open FStarC.PSMap

type ext_state =
  | E : map : psmap string -> ext_state

(* Default extension options *)
let defaults = [
  ("context_pruning", "true");
]

let init : ext_state =
  E <| List.fold_right (fun (k,v) m -> psmap_add m k v)
         defaults
         (psmap_empty ())

let cur_state = alloc init

(* Set a key-value pair in the map *)
let set (k:key) (v:value) : unit =
  cur_state := E (psmap_add (!cur_state).map k v)

(* Get the value from the map, or return "" if not there *)
let get (k:key) : value =
  let r = 
    match psmap_try_find (!cur_state).map k with
    | None -> ""
    | Some v -> v
  in
  r

let enabled (k:key) : bool =
  let v = get k in
  let v = String.lowercase v in
  v <> "" && not (v = "off" || v = "false" || v = "0")

(* Find a home *)
let is_prefix (s1 s2 : string) : ML bool =
  let open FStarC.String in
  let l1 = length s1 in
  let l2 = length s2 in
  l2 >= l1 && substring s2 0 l1 = s1

(* Get a list of all KV pairs that "begin" with k, considered
as a namespace. *)
let getns (ns:string) : list (key & value) =
  let f k v acc =
    if (ns^":") `is_prefix` k
    then (k, v) :: acc
    else acc
  in
  psmap_fold (!cur_state).map f []

let all () : list (key & value) =
  let f k v acc = (k, v) :: acc in
  psmap_fold (!cur_state).map f []

let save () : ext_state =
  !cur_state

let restore (s:ext_state) : unit =
  cur_state := s;
  ()

let reset () : unit =
  cur_state := init
