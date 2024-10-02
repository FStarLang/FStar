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
(** Propositional sets (on any types): membership is a predicate *)
module FStar.TSet

#set-options "--initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0"

(*
 * AR: mark it must_erase_for_extraction temporarily until CMI comes in
 *)
[@@must_erase_for_extraction; erasable]
val set (a:Type u#a) : Type u#(max 1 a)

val equal (#a:Type) (s1:set a) (s2:set a) : prop

(* destructors *)

val mem : 'a -> set 'a -> prop

(* constructors *)
val empty      : #a:Type -> Tot (set a)
val singleton  : #a:Type -> x:a -> Tot (set a)
val union      : #a:Type -> x:set a -> y:set a -> Tot (set a)
val intersect  : #a:Type -> x:set a -> y:set a -> Tot (set a)
val complement : #a:Type -> x:set a -> Tot (set a)
val intension  : #a:Type -> (a -> prop) -> Tot (set a)

(* ops *)
let subset (#a:Type) (s1:set a) (s2:set a) : Type0 = forall x. mem x s1 ==> mem x s2

(* Properties *)
val mem_empty: #a:Type -> x:a -> Lemma
   (requires True)
   (ensures (~ (mem x empty)))
   [SMTPat (mem x empty)]

val mem_singleton: #a:Type -> x:a -> y:a -> Lemma
   (requires True)
   (ensures (mem y (singleton x) <==> (x==y)))
   [SMTPat (mem y (singleton x))]

val mem_union: #a:Type -> x:a -> s1:set a -> s2:set a -> Lemma
   (requires True)
   (ensures (mem x (union s1 s2) == (mem x s1 \/ mem x s2)))
   [SMTPat (mem x (union s1 s2))]

val mem_intersect: #a:Type -> x:a -> s1:set a -> s2:set a -> Lemma
   (requires True)
   (ensures (mem x (intersect s1 s2) == (mem x s1 /\ mem x s2)))
   [SMTPat (mem x (intersect s1 s2))]

val mem_complement: #a:Type -> x:a -> s:set a -> Lemma
   (requires True)
   (ensures (mem x (complement s) == ~(mem x s)))
   [SMTPat (mem x (complement s))]

val mem_subset: #a:Type -> s1:set a -> s2:set a -> Lemma
   (requires (forall x. mem x s1 ==> mem x s2))
   (ensures (subset s1 s2))
   [SMTPat (subset s1 s2)]

val subset_mem: #a:Type -> s1:set a -> s2:set a -> Lemma
   (requires (subset s1 s2))
   (ensures (forall x. mem x s1 ==> mem x s2))
   [SMTPat (subset s1 s2)]

val mem_intension (#a:Type) (x:a) (f:(a -> prop))
: Lemma 
  (ensures (mem x (intension f) == f x))
  [SMTPat (mem x (intension f))]

(* extensionality *)

val lemma_equal_intro: #a:Type -> s1:set a -> s2:set a -> Lemma
    (requires  (forall x. mem x s1 <==> mem x s2))
    (ensures (equal s1 s2))
    [SMTPat (equal s1 s2)]

val lemma_equal_elim: #a:Type -> s1:set a -> s2:set a -> Lemma
    (requires (equal s1 s2))
    (ensures  (s1 == s2))
    [SMTPat (equal s1 s2)]

val lemma_equal_refl: #a:Type -> s1:set a -> s2:set a -> Lemma
    (requires (s1 == s2))
    (ensures  (equal s1 s2))
    [SMTPat (equal s1 s2)]

val tset_of_set (#a:eqtype) (s:Set.set a) : Tot (set a)

val lemma_mem_tset_of_set (#a:eqtype) (s:Set.set a) (x:a)
  :Lemma (requires True)
         (ensures  (Set.mem x s <==> mem x (tset_of_set s)))
         [SMTPat (mem x (tset_of_set s))]

val filter (#a:Type) (f:a -> Type0) (s:set a) : Tot (set a)

val lemma_mem_filter (#a:Type) (f:(a -> Type0)) (s:set a) (x:a)
  :Lemma (requires True)
         (ensures  (mem x (filter f s) <==> mem x s /\ f x))
         [SMTPat (mem x (filter f s))]

val map (#a:Type) (#b:Type) (f:a -> Tot b) (s:set a) : Tot (set b)

val lemma_mem_map (#a:Type) (#b:Type) (f:(a -> Tot b)) (s:set a) (x:b)
  :Lemma ((exists (y:a). {:pattern (mem y s)} mem y s /\ x == f y) <==> mem x (map f s))
         [SMTPat (mem x (map f s))]

#reset-options
let rec as_set' (#a:Type) (l:list a) : Tot (set a) =
  match l with
  | [] -> empty
  | hd::tl -> union (singleton hd) (as_set' tl)


(* unfold let as_set (#a:Type) (l:list a) : set a = *)
(*   Prims.norm [zeta; iota; delta_only ["FStar.TSet.as_set'"]] (as_set' l) *)
