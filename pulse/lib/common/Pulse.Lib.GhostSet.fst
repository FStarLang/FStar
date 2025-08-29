(*
   Copyright 2025 Microsoft Research

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

module Pulse.Lib.GhostSet
open FStar.List.Tot { (@) }

let rec mem_as_set' f x = function
  | [] -> ()
  | y::l -> mem_as_set' f x l

let decide_eq_f x y = IndefiniteDescription.strong_excluded_middle (x == y)

let is_finite x = exists l. x == as_set l
let is_finite_prop x = ()
let is_finite_elim x =
  IndefiniteDescription.indefinite_description_ghost _ (fun l -> x == as_set l)

let is_finite_empty t =
  lemma_equal_intro (empty #t) (as_set [])

let is_finite_singleton f x =
  lemma_equal_intro (singleton f x) (as_set [x])

let rec list_filterP #t (p: t->prop) (xs: list t) :
    GTot (ys:list t { forall x. List.memP x ys <==> p x /\ List.memP x xs }) =
  match xs with
  | [] -> []
  | x::xs ->
    if IndefiniteDescription.strong_excluded_middle (p x) then
      x :: list_filterP p xs
    else
      list_filterP p xs

let is_finite_union_r #t (x y: set t) =
  introduce is_finite (union x y) ==> is_finite x with _.
  let xy' = is_finite_elim (union x y) in
  assert (forall a. mem a (union x y) <==> List.memP a xy');
  let x' = list_filterP (fun a -> mem a x) xy' in
  lemma_equal_intro x (as_set x')

let is_finite_union_l #t (x y: set t) =
  introduce is_finite x /\ is_finite y ==> is_finite (union x y) with _.
  let x' = is_finite_elim x in
  let y' = is_finite_elim y in
  List.append_memP_forall x' y';
  lemma_equal_intro (union x y) (as_set (x' @ y'))

let is_finite_union x y =
  is_finite_union_l x y;
  is_finite_union_r x y;
  lemma_equal_intro (union x y) (union y x);
  is_finite_union_r y x

let is_finite_intersect_r #t (x y: set t) =
  introduce is_finite x ==> is_finite (intersect x y) with _.
  let x' = is_finite_elim x in
  let xy' = list_filterP (fun a -> mem a y) x' in
  lemma_equal_intro (intersect x y) (as_set xy')

let is_finite_intersect x y =
  is_finite_intersect_r x y;
  lemma_equal_intro (intersect x y) (intersect y x);
  is_finite_intersect_r y x