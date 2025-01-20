(*
   Copyright 2015 Chantal Keller and Catalin Hritcu, Microsoft Research and Inria

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.

   Authors: Chantal Keller, Catalin Hritcu, Aseem Rastogi, Nikhil Swamy
*)

(* Defining accessibility predicates and well-founded recursion like in Coq
   https://coq.inria.fr/library/Coq.Init.Wf.html
*)

module FStar.WellFounded

#set-options "--warn_error -242" //inner let recs not encoded to SMT; ok

let binrel (a:Type) = a -> a -> Type

(*
 * The accessibility relation
 * -- Marked erasable, since this is a singleton type anyway
 * -- Erasability also simplifies proofs that use accessibility in
 *    with axioms like indefinitedescription
 *)
[@@ erasable]
noeq
type acc (#a:Type u#a) (r:binrel u#a u#r a) (x:a) : Type u#(max a r) =
  | AccIntro : access_smaller:(y:a -> r y x -> acc r y) -> acc r x

(*
 * A binrel r is well-founded if every element is accessible
 *)
let well_founded (#a:Type u#a) (r:binrel u#a u#r a) = x:a -> acc r x

(*
 * Accessibility predicates can be used for implementing
 *   total fix points
 *)
let rec fix_F (#aa:Type) (#r:binrel aa) (#p:(aa -> Type))
              (f: (x:aa -> (y:aa -> r y x -> p y) -> p x))
              (x:aa) (a:acc r x)
  : Tot (p x) (decreases a)
  = f x (fun y h -> fix_F f y (a.access_smaller y h))

let fix (#aa:Type) (#r:binrel aa) (rwf:well_founded r)
        (p:aa -> Type) (f:(x:aa -> (y:aa -> r y x -> p y) -> p x))
        (x:aa)
  : p x
  = fix_F f x (rwf x)

let is_well_founded (#a:Type) (rel:binrel a) =
  forall (x:a). squash (acc rel x)

let well_founded_relation (a:Type) = rel:binrel a{is_well_founded rel}

unfold
let as_well_founded (#a:Type u#a)
                    (#rel:binrel u#a u#r a)
                    (f:well_founded rel)
  : well_founded_relation a
  = introduce forall (x:a). squash (acc rel x)
    with FStar.Squash.return_squash (FStar.Squash.return_squash (f x));
    rel

open FStar.IndefiniteDescription

(*
 * Proofs that subrelation and inverse image commute with well-foundedness
 *
 * Reference: Constructing Recursion Operators in Type Theory, L. Paulson  JSC (1986) 2, 325-355
 *)
let subrelation_wf (#a:Type) (#r #sub_r:binrel a)
  (sub_w:(x:a -> y:a -> sub_r x y -> r x y))
  (r_wf:well_founded r)
  : well_founded sub_r
  = let rec aux (x:a) (acc_r:acc r x) : Tot (acc sub_r x) (decreases acc_r) =
      AccIntro (fun y sub_r_y_x ->
        aux y
          (match acc_r with
           | AccIntro f -> f y (sub_w y x sub_r_y_x))) in
    fun x -> aux x (r_wf x)

let subrelation_squash_wf (#a:Type u#a)
                          (#r:binrel u#a u#r a)
                          (#sub_r:binrel u#a u#sr a)
                          (sub_w:(x:a -> y:a -> sub_r x y -> squash (r x y)))
                          (r_wf:well_founded r)
  : Lemma (is_well_founded sub_r)
  = introduce forall (x:a). squash (acc sub_r x)
    with (
      let rec acc_y (x:a) (acc_r:acc r x) (y:a) (p:sub_r y x)
        : Tot (acc sub_r y)
              (decreases acc_r)
        = AccIntro (acc_y y (acc_r.access_smaller
                                   y
                                   (elim_squash (sub_w y x p))))
      in
      FStar.Squash.return_squash (FStar.Squash.return_squash (AccIntro (acc_y x (r_wf x))))
    )

unfold
let subrelation_as_wf (#a:Type u#a) (#r #sub_r:binrel u#a u#r a)
  (sub_w:(x:a -> y:a -> sub_r x y -> squash (r x y)))
  (r_wf:well_founded r)
  : well_founded_relation a
  = subrelation_squash_wf sub_w r_wf;
    sub_r

let inverse_image (#a:Type u#a) (#b:Type u#b) (r_b:binrel u#b u#r b) (f:a -> b) : binrel u#a u#r a =
  fun x y -> r_b (f x) (f y)

let inverse_image_wf (#a:Type u#a) (#b:Type u#b) (#r_b:binrel u#b u#r b)
  (f:a -> b)
  (r_b_wf:well_founded r_b)
  : well_founded (inverse_image r_b f)
  = let rec aux (x:a) (acc_r_b:acc r_b (f x))
      : Tot (acc (inverse_image r_b f) x)
            (decreases acc_r_b) =
      AccIntro (fun y p -> aux y (acc_r_b.access_smaller (f y) p))
    in
    fun x -> aux x (r_b_wf (f x))
