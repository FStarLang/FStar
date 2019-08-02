(*
   Copyright 2008-2018 Microsoft Research

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
(*
Benchmark problem from Dagstuhl Seminar 16131
http://www.dagstuhl.de/en/program/calendar/semhp/?semnr=16131

(we also solved this in Dafny, Liquid Haskell, Why3, and Synquid)
*)

module Coincidence

val mem: int -> list int -> Tot bool
let rec mem a l =
  match l with
  | [] -> false
  | hd::tl -> hd=a || mem a tl


val sorted: list int -> Tot bool
let rec sorted l =
  match l with
  | x::y::xs -> x < y && sorted (y::xs)
  | _ -> true


val lemma1 : y:int -> xs:list int ->
  Lemma (requires (sorted xs && (xs = [] || y < Cons.hd xs)))
        (ensures (not (mem y xs)))
let rec lemma1 y xs =
  match xs with
  | []     -> ()
  | x::xs' -> lemma1 y xs'


val coincidence : xs:(list int){sorted xs} -> ys : (list int){sorted ys} ->
        Tot (zs:(list int){forall z. mem z zs <==> (mem z xs && mem z ys)})
let rec coincidence xs ys =
  match xs, ys with
  | x::xs', y::ys' ->
    if x = y then              x :: coincidence xs' ys'
    else if x < y then (lemma1 x ys; coincidence xs' ys)
    else               (lemma1 y xs; coincidence xs  ys')
  | _ -> []
