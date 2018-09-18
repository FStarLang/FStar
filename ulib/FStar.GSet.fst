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

(** Computatiional sets (on Types): membership is a boolean function *)
module FStar.GSet
#set-options "--initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0"
open FStar.FunctionalExtensionality

// abstract let set (a:Type u#x) : Tot (Type u#x) = a -> GTot bool
abstract
let set (a: Type) : Tot Type = a -> GTot bool
abstract
type equal (#a: Type) (s1: set a) (s2: set a) = gfeq s1 s2

(* destructors *)
abstract
val mem: #a: Type -> a -> set a -> GTot bool
let mem #a x s = s x

(* constructors *)
abstract
val empty: #a: Type -> Tot (set a)
abstract
val singleton: #a: Type -> a -> Tot (set a)
abstract
val union: #a: Type -> set a -> set a -> Tot (set a)
abstract
val intersect: #a: Type -> set a -> set a -> Tot (set a)
abstract
val complement: #a: Type -> set a -> Tot (set a)

let empty = fun #a x -> false
let singleton #a x = fun y -> StrongExcludedMiddle.strong_excluded_middle (y == x)
let union #a s1 s2 = fun x -> s1 x || s2 x
let intersect #a s1 s2 = fun x -> s1 x && s2 x
let complement #a s = fun x -> not (s x)

(* a property about sets *)
let disjoint (#a: Type) (s1: set a) (s2: set a) = equal (intersect s1 s2) empty

(* ops *)
type subset (#a: Type) (s1: set a) (s2: set a) : Type0 = forall x. mem x s1 ==> mem x s2

(* Properties *)
abstract
val mem_empty: #a: Type -> x: a ->
  Lemma (requires True) (ensures (not (mem x empty))) [SMTPat (mem x empty)]
abstract
val mem_singleton: #a: Type -> x: a -> y: a ->
  Lemma (requires True) (ensures (mem y (singleton x) <==> (x == y))) [SMTPat (mem y (singleton x))]
abstract
val mem_union: #a: Type -> x: a -> s1: set a -> s2: set a ->
  Lemma (requires True)
    (ensures (mem x (union s1 s2) = (mem x s1 || mem x s2)))
    [SMTPat (mem x (union s1 s2))]
abstract
val mem_intersect: #a: Type -> x: a -> s1: set a -> s2: set a ->
  Lemma (requires True)
    (ensures (mem x (intersect s1 s2) = (mem x s1 && mem x s2)))
    [SMTPat (mem x (intersect s1 s2))]
abstract
val mem_complement: #a: Type -> x: a -> s: set a ->
  Lemma (requires True)
    (ensures (mem x (complement s) = not (mem x s)))
    [SMTPat (mem x (complement s))]
abstract
val mem_subset: #a: Type -> s1: set a -> s2: set a ->
  Lemma (requires (forall x. mem x s1 ==> mem x s2))
    (ensures (subset s1 s2))
    [SMTPat (subset s1 s2)]
abstract
val subset_mem: #a: Type -> s1: set a -> s2: set a ->
  Lemma (requires (subset s1 s2))
    (ensures (forall x. mem x s1 ==> mem x s2))
    [SMTPat (subset s1 s2)]

let mem_empty #a x = ()
let mem_singleton #a x y = ()
let mem_union #a x s1 s2 = ()
let mem_intersect #a x s1 s2 = ()
let mem_complement #a x s = ()
let subset_mem #a s1 s2 = ()
let mem_subset #a s1 s2 = ()

(* extensionality *)
abstract
val lemma_equal_intro: #a: Type -> s1: set a -> s2: set a ->
  Lemma (requires (forall x. mem x s1 = mem x s2)) (ensures (equal s1 s2)) [SMTPat (equal s1 s2)]
abstract
val lemma_equal_elim: #a: Type -> s1: set a -> s2: set a ->
  Lemma (requires (equal s1 s2)) (ensures (s1 == s2)) [SMTPat (equal s1 s2)]
abstract
val lemma_equal_refl: #a: Type -> s1: set a -> s2: set a ->
  Lemma (requires (s1 == s2)) (ensures (equal s1 s2)) [SMTPat (equal s1 s2)]

let lemma_equal_intro #a s1 s2 = ()
let lemma_equal_elim #a s1 s2 = ()
let lemma_equal_refl #a s1 s2 = ()

let disjoint_not_in_both (a: Type) (s1: set a) (s2: set a)
  : Lemma (requires (disjoint s1 s2))
    (ensures (forall (x: a). {:pattern (mem x s1)\/(mem x s2)} mem x s1 ==> ~(mem x s2)))
    [SMTPat (disjoint s1 s2)] =
  let f (x: a) : Lemma (~(mem x (intersect s1 s2))) = () in
  FStar.Classical.forall_intro f

(* Converting lists to sets *)
#reset-options
//restore fuel usage here

val as_set': #a: Type -> list a -> Tot (set a)
let rec as_set' #a l =
  match l with
  | [] -> empty
  | hd :: tl -> union (singleton hd) (as_set' tl)

let lemma_disjoint_subset (#a: Type) (s1: set a) (s2: set a) (s3: set a)
  : Lemma (requires (disjoint s1 s2 /\ subset s3 s1)) (ensures (disjoint s3 s2)) = ()

abstract
let comprehend (#a: Type) (f: (a -> GTot bool)) : Tot (set a) = f

abstract
let comprehend_mem (#a: Type) (f: (a -> GTot bool)) (x: a)
  : Lemma (mem x (comprehend f) == f x) [SMTPat (mem x (comprehend f))] = ()

abstract
let of_set (#a: eqtype) (f: Set.set a) : Tot (set a) = (fun x -> Set.mem x f)

abstract
let mem_of_set (#a: eqtype) (f: Set.set a) (x: a)
  : Lemma (mem x (of_set f) <==> Set.mem x f) [SMTPat (mem x (of_set f))] = ()

