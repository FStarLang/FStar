(*
   Copyright 2008-2025 Microsoft Research

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
module LetRecRefinedFunctionResult

(* An [ensures] on a computation type is a refinement on its result. When the
   result is itself an arrow, the annotation of a [let rec] is therefore a
   *refinement of an arrow*, and splitting that type into binders must not
   descend past the refinement: doing so drops the predicate, i.e. the
   definition's postcondition. This used to happen twice --- once when moving
   the annotation onto the body, so the body was checked against the unrefined
   arrow, and once when giving a type to the recursive occurrence, so a call to
   it did not know its own postcondition. *)

assume val t : Type0
assume val q : (nat -> t) -> prop
assume val bdy : (nat -> t) -> (nat -> t)
assume val lem (g: nat -> t) : Lemma (ensures q (bdy g))
assume val base : nat -> t

(* The body's facts must reach the postcondition. *)
let rec f1 (n:nat) : Pure (nat -> t) (requires True) (ensures fun fp -> q fp) (decreases n) =
  let _ = (if n = 0 then () else (let _ = f1 (n-1) in ())) in
  let _ = lem base in
  bdy base

(* Same, written as a refined [Tot] result. *)
let rec f2 (n:nat) : Tot (fp: (nat -> t) { q fp }) (decreases n) =
  let _ = (if n = 0 then () else (let _ = f2 (n-1) in ())) in
  let _ = lem base in
  bdy base

(* The recursive occurrence must have the refined result type too. *)
let rec f3 (n:nat) : Pure (nat -> t) (requires True) (ensures fun fp -> q fp) =
  if n = 0
  then (let _ = lem base in bdy base)
  else f3 (n - 1)

(* Mutual recursion, and a non-arrow result for contrast. *)
assume val qn : nat -> prop
assume val lemn (u:unit) : Lemma (ensures qn 3)

let rec g1 (n:nat) : Pure nat (requires True) (ensures fun fp -> qn fp) (decreases n) =
  let _ = (if n = 0 then () else (let _ = g1 (n-1) in ())) in
  let _ = lemn () in
  3
