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

module FStarC.Common

open FStarC
open FStarC.Effect
open FStarC.PSMap

module List = FStarC.List
module BU = FStarC.Util
module SB = FStarC.StringBuffer

let snapshot (push: 'a -> 'b) (stackref: ref (list 'c)) (arg: 'a) : (int & 'b) = BU.atomically (fun () ->
  let len : int = List.length !stackref in
  let arg' = push arg in
  (len, arg'))

let rollback (pop: unit -> 'a) (stackref: ref (list 'c)) (depth: option int) =
  let rec aux n : 'a =
    if n <= 0 then failwith "Too many pops"
    else if n = 1 then pop ()
    else (ignore (pop ()); aux (n - 1)) in
  let curdepth = List.length !stackref in
  let n = match depth with Some d -> curdepth - d | None -> 1 in
  BU.atomically (fun () -> aux n)

// This function is separate to make it easier to put breakpoints on it
let raise_failed_assertion msg =
  failwith (Format.fmt1 "Assertion failed: %s" msg)

let runtime_assert b msg =
  if not b then raise_failed_assertion msg

let __string_of_list (delim:string) (f : 'a -> string) (l : list 'a) : string =
  match l with
  | [] -> "[]"
  | x::xs ->
    let strb = SB.create 80 in
    strb |> SB.add "[" |> SB.add (f x) |> ignore;
    List.iter (fun x ->
                strb |> SB.add delim |> SB.add (f x) |> ignore
               ) xs ;
    strb |> SB.add "]" |> ignore;
    SB.contents strb

(* Why two? This function was added during a refactoring, and
both variants existed. We cannot simply move to ";" since that is a
breaking change to anything that parses F* source code (like Vale). *)
let string_of_list  f l = __string_of_list ", " f l
let string_of_list' f l = __string_of_list "; " f l

let list_of_option (o:option 'a) : list 'a =
    match o with
    | None -> []
    | Some x -> [x]

let string_of_option f = function
  | None -> "None"
  | Some x -> "Some " ^ f x

(* Was List.init, but F* doesn't have this in ulib *)
let tabulate (n:int) (f : int -> 'a) : list 'a =
  let rec aux i : list 'a =
    if i < n
    then f i :: aux (i + 1)
    else []
  in aux 0

(** max_prefix f xs returns (l, r) such that
  * every x in l satisfies f
  * l@r == xs
  * and l is the largest list satisfying that
  *)
let rec max_prefix (f : 'a -> bool) (xs : list 'a) : list 'a & list 'a =
  match xs with
  | [] -> [], []
  | x::xs when f x ->
    let l, r = max_prefix f xs in
    (x::l, r)
  | x::xs ->
    ([], x::xs)

(** max_suffix f xs returns (l, r) such that
  * every x in r satisfies f
  * l@r == xs
  * and r is the largest list satisfying that
  *)
let max_suffix (f : 'a -> bool) (xs : list 'a) : list 'a & list 'a =
  let rec aux acc xs : list 'a & list 'a =
    match xs with
    | [] -> acc, []
    | x::xs when f x ->
      aux (x::acc) xs
    | x::xs ->
      (acc, x::xs)
  in
  xs |> List.rev |> aux [] |> (fun (xs, ys) -> List.rev ys, xs)

let rec eq_list (f: 'a -> 'a -> bool) (l1 l2 : list 'a)
  : bool
  = match l1, l2 with
    | [], [] -> true
    | [], _ | _, [] -> false
    | x1::t1, x2::t2 -> f x1 x2 && eq_list f t1 t2

let psmap_to_list m =
  psmap_fold m (fun k v a -> (k,v)::a) []
let psmap_keys m =
  psmap_fold m (fun k v a -> k::a) []
let psmap_values m =
  psmap_fold m (fun k v a -> v::a) []

let option_to_list = function
  | None -> []
  | Some x -> [x]
