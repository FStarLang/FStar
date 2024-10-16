(*
   Copyright 2008-2014 Nikhil Swamy, Aseem Rastogi,
                       Microsoft Research, University of Maryland

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

module FStar.Set
(** Computational sets (on eqtypes): membership is a boolean function *)
#set-options "--initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0"

val set (a:eqtype)
  : Type0

val equal (#a:eqtype) (s1:set a) (s2:set a)
  : Type0

(* destructors *)

val mem (#a:eqtype) (x:a) (s:set a)
  : Tot bool

(* constructors *)
val empty (#a:eqtype)
  : Tot (set a)

val singleton (#a:eqtype) (x:a)
  : Tot (set a)

val union      : #a:eqtype -> set a -> set a -> Tot (set a)
val intersect  : #a:eqtype -> set a -> set a -> Tot (set a)
val complement : #a:eqtype -> set a -> Tot (set a)
val intension  : #a:eqtype -> (a -> Tot bool) -> GTot (set a)

(* Derived functions *)

let disjoint (#a:eqtype) (s1: set a) (s2: set a) =
  equal (intersect s1 s2) empty

let subset (#a:eqtype) (s1:set a) (s2:set a) =
  forall x. mem x s1 ==> mem x s2

let add (#a:eqtype) (x:a) (s:set a) : set a =
  union s (singleton x)

let remove (#a:eqtype) (x:a) (s:set a) : set a =
  intersect s (complement (singleton x))

(* Properties *)
val mem_empty: #a:eqtype -> x:a -> Lemma
   (requires True)
   (ensures (not (mem x empty)))
   [SMTPat (mem x empty)]

val mem_singleton: #a:eqtype -> x:a -> y:a -> Lemma
   (requires True)
   (ensures (mem y (singleton x) = (x=y)))
   [SMTPat (mem y (singleton x))]

val mem_union: #a:eqtype -> x:a -> s1:set a -> s2:set a -> Lemma
   (requires True)
   (ensures (mem x (union s1 s2) = (mem x s1 || mem x s2)))
   [SMTPat (mem x (union s1 s2))]

val mem_intersect: #a:eqtype -> x:a -> s1:set a -> s2:set a -> Lemma
   (requires True)
   (ensures (mem x (intersect s1 s2) = (mem x s1 && mem x s2)))
   [SMTPat (mem x (intersect s1 s2))]

val mem_complement: #a:eqtype -> x:a -> s:set a -> Lemma
   (requires True)
   (ensures (mem x (complement s) = not (mem x s)))
   [SMTPat (mem x (complement s))]

val mem_intension: #a:eqtype -> x:a -> f:(a -> Tot bool) -> Lemma
  (requires True)
  (ensures (mem x (intension f) = f x))

val mem_subset: #a:eqtype -> s1:set a -> s2:set a -> Lemma
   (requires (forall x. mem x s1 ==> mem x s2))
   (ensures (subset s1 s2))
   [SMTPat (subset s1 s2)]

val subset_mem: #a:eqtype -> s1:set a -> s2:set a -> Lemma
   (requires (subset s1 s2))
   (ensures (forall x. mem x s1 ==> mem x s2))
   [SMTPat (subset s1 s2)]

(* extensionality *)
val lemma_equal_intro: #a:eqtype -> s1:set a -> s2:set a -> Lemma
    (requires  (forall x. mem x s1 = mem x s2))
    (ensures (equal s1 s2))
    [SMTPat (equal s1 s2)]

val lemma_equal_elim: #a:eqtype -> s1:set a -> s2:set a -> Lemma
    (requires (equal s1 s2))
    (ensures  (s1 == s2))
    [SMTPat (equal s1 s2)]

val lemma_equal_refl: #a:eqtype -> s1:set a -> s2:set a -> Lemma
    (requires (s1 == s2))
    (ensures  (equal s1 s2))
    [SMTPat (equal s1 s2)]

val disjoint_not_in_both (a:eqtype) (s1:set a) (s2:set a)
  : Lemma
      (requires (disjoint s1 s2))
      (ensures (forall (x:a).{:pattern (mem x s1) \/ (mem x s2)} mem x s1 ==> ~(mem x s2)))
      [SMTPat (disjoint s1 s2)]

(* Converting lists to sets *)

(* WHY IS THIS HERE? It is not strictly part of the interface *)
#reset-options //restore fuel usage here
let rec as_set' (#a:eqtype) (l:list a) : set a =
  match l with
  | [] -> empty
  | hd::tl -> union (singleton hd) (as_set' tl)

unfold
let as_set (#a:eqtype) (l:list a) = normalize_term (as_set' l)

let lemma_disjoint_subset (#a:eqtype) (s1:set a) (s2:set a) (s3:set a)
  : Lemma (requires (disjoint s1 s2 /\ subset s3 s1))
          (ensures  (disjoint s3 s2))
  = ()
