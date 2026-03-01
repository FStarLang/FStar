(*
   Copyright 2008-2017 Microsoft Research

   Authors: Aseem Rastogi, Nikhil Swamy, Jonathan Protzenko

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
module FStarC.Path

open FStarC.Class.Deq

let rec is_under {| deq 'a |} (p1 p2 : path 'a) : bool =
  match p1, p2 with
  | _, [] -> true
  | [], _ -> false
  | h1::t1, h2::t2 -> h1 =? h2 && is_under t1 t2

let search_forest #a #q {| deq a |} p f =
  let roots, def = f in
  let rec aux (roots : list (path a & q)) : q =
    match roots with
    | [] -> def
    | (r, q)::rs -> if p `is_under` r then q else aux rs
  in
  aux roots
