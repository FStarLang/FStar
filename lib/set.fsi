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
#set-options "--initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0"

type set : Type -> Type

(* Destructors *)
val mem : #a:Type -> a -> set a -> Tot bool

(* Constructors *)
val empty      : #a:Type -> Tot (set a)
val singleton  : #a:Type -> a -> Tot (set a)
val union      : #a:Type -> set a -> set a -> Tot (set a)
val intersect  : #a:Type -> set a -> set a -> Tot (set a)
val complement : #a:Type -> set a -> Tot (set a)

(* Ops *)
val subset     : #a:Type -> set a -> set a -> Tot bool

(* Properties *)
val mem_empty: #a:Type -> x:a -> Lemma
   (requires True)
   (ensures (not (mem x empty)))
   [SMTPat (mem x empty)]

val mem_singleton: #a:Type -> x:a -> y:a -> Lemma
   (requires True)
   (ensures (mem y (singleton x) = (x=y)))
   [SMTPat (mem y (singleton x))]

val mem_union: #a:Type -> x:a -> s1:set a -> s2:set a -> Lemma
   (requires True)
   (ensures (mem x (union s1 s2) = (mem x s1 || mem x s2)))
   [SMTPat (mem x (union s1 s2))]

val mem_intersect: #a:Type -> x:a -> s1:set a -> s2:set a -> Lemma
   (requires True)
   (ensures (mem x (intersect s1 s2) = (mem x s1 && mem x s2)))
   [SMTPat (mem x (intersect s1 s2))]

val mem_complement: #a:Type -> x:a -> s:set a -> Lemma
   (requires True)
   (ensures (mem x (complement s) = not(mem x s)))
   [SMTPat (mem x (complement s))]

val mem_subset: #a:Type -> s1:set a -> s2:set a -> Lemma
   (requires (forall x. mem x s1 ==> mem x s2))
   (ensures (subset s1 s2))
   [SMTPat (subset s1 s2)]

val subset_mem: #a:Type -> s1:set a -> s2:set a -> Lemma
   (requires (subset s1 s2))
   (ensures (forall x. mem x s1 ==> mem x s2))
   [SMTPat (subset s1 s2)]

(* Extensionality *)
type Equal : #a:Type -> set a -> set a -> Type
val lemma_equal_intro: #a:Type -> s1:set a -> s2:set a -> Lemma
    (requires  (forall x. mem x s1 = mem x s2))
    (ensures (Equal s1 s2))
    [SMTPatT (Equal s1 s2)]

val lemma_equal_elim: #a:Type -> s1:set a -> s2:set a -> Lemma
    (requires (Equal s1 s2))
    (ensures  (s1 = s2))
    [SMTPatT (Equal s1 s2)]

val lemma_equal_refl: #a:Type -> s1:set a -> s2:set a -> Lemma 
    (requires (s1 = s2))
    (ensures  (Equal s1 s2))
    [SMTPatT (Equal s1 s2)]
