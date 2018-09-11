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
(** Computatiional sets (on eqtypes): membership is a boolean function *)
module FStar.Set
#set-options "--initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0"
open FStar.FunctionalExtensionality

abstract type set (a:Type u#a{hasEq a}) :Type u#a = a -> Tot bool
abstract type equal (#a:eqtype) (s1:set a) (s2:set a) = feq s1 s2

(* destructors *)

abstract val mem : #a:eqtype -> a -> set a -> Tot bool
let mem #a x s = s x

(* constructors *)
abstract val empty      : #a:eqtype -> Tot (set a)
abstract val singleton  : #a:eqtype -> a -> Tot (set a)
abstract val union      : #a:eqtype -> set a -> set a -> Tot (set a)
abstract val intersect  : #a:eqtype -> set a -> set a -> Tot (set a)
abstract val complement : #a:eqtype -> set a -> Tot (set a)

let empty              = fun #a x -> false
let singleton #a x     = fun y -> y = x
let union #a s1 s2     = fun x -> s1 x || s2 x
let intersect #a s1 s2 = fun x -> s1 x && s2 x
let complement #a s    = fun x -> not (s x)

(* a property about sets *)
let disjoint (#a:eqtype) (s1: set a) (s2: set a) =
  equal (intersect s1 s2) empty


(* ops *)
type subset (#a:eqtype) (s1:set a) (s2:set a) :Type0 = forall x. mem x s1 ==> mem x s2

(* Properties *)
abstract val mem_empty: #a:eqtype -> x:a -> Lemma
   (requires True)
   (ensures (not (mem x empty)))
   [SMTPat (mem x empty)]

abstract val mem_singleton: #a:eqtype -> x:a -> y:a -> Lemma
   (requires True)
   (ensures (mem y (singleton x) = (x=y)))
   [SMTPat (mem y (singleton x))]

abstract val mem_union: #a:eqtype -> x:a -> s1:set a -> s2:set a -> Lemma
   (requires True)
   (ensures (mem x (union s1 s2) = (mem x s1 || mem x s2)))
   [SMTPat (mem x (union s1 s2))]

abstract val mem_intersect: #a:eqtype -> x:a -> s1:set a -> s2:set a -> Lemma
   (requires True)
   (ensures (mem x (intersect s1 s2) = (mem x s1 && mem x s2)))
   [SMTPat (mem x (intersect s1 s2))]

abstract val mem_complement: #a:eqtype -> x:a -> s:set a -> Lemma
   (requires True)
   (ensures (mem x (complement s) = not (mem x s)))
   [SMTPat (mem x (complement s))]

abstract val mem_subset: #a:eqtype -> s1:set a -> s2:set a -> Lemma
   (requires (forall x. mem x s1 ==> mem x s2))
   (ensures (subset s1 s2))
   [SMTPat (subset s1 s2)]

abstract val subset_mem: #a:eqtype -> s1:set a -> s2:set a -> Lemma
   (requires (subset s1 s2))
   (ensures (forall x. mem x s1 ==> mem x s2))
   [SMTPat (subset s1 s2)]

let mem_empty      #a x       = ()
let mem_singleton  #a x y     = ()
let mem_union      #a x s1 s2 = ()
let mem_intersect  #a x s1 s2 = ()
let mem_complement #a x s     = ()
let subset_mem     #a s1 s2   = ()
let mem_subset     #a s1 s2   = ()

(* extensionality *)

abstract val lemma_equal_intro: #a:eqtype -> s1:set a -> s2:set a -> Lemma
    (requires  (forall x. mem x s1 = mem x s2))
    (ensures (equal s1 s2))
    [SMTPat (equal s1 s2)]

abstract val lemma_equal_elim: #a:eqtype -> s1:set a -> s2:set a -> Lemma
    (requires (equal s1 s2))
    (ensures  (s1 == s2))
    [SMTPat (equal s1 s2)]

abstract val lemma_equal_refl: #a:eqtype -> s1:set a -> s2:set a -> Lemma
    (requires (s1 == s2))
    (ensures  (equal s1 s2))
    [SMTPat (equal s1 s2)]

let lemma_equal_intro #a s1 s2 = ()
let lemma_equal_elim  #a s1 s2 = ()
let lemma_equal_refl  #a s1 s2 = ()

let disjoint_not_in_both (a:eqtype) (s1:set a) (s2:set a) :
  Lemma
    (requires (disjoint s1 s2))
    (ensures (forall (x:a).{:pattern (mem x s1) \/ (mem x s2)} mem x s1 ==> ~(mem x s2)))
  [SMTPat (disjoint s1 s2)]
= let f (x:a) : Lemma (~(mem x (intersect s1 s2))) = () in
  FStar.Classical.forall_intro f

(* Converting lists to sets *)
#reset-options //restore fuel usage here
type eqtype = a:Type0{hasEq a}

val as_set': #a:eqtype -> list a -> Tot (set a)
let rec as_set' #a l = match l with
  | [] -> empty
  | hd::tl -> union (singleton hd) (as_set' tl)

unfold val as_set:  #a:eqtype -> l:list a -> Tot (set a)
let as_set (#a:eqtype) (l:list a) = normalize_term (as_set' l)

assume val lemma_disjoint_subset (#a:eqtype) (s1:set a) (s2:set a) (s3:set a)
  :Lemma (requires (disjoint s1 s2 /\ subset s3 s1))
         (ensures  (disjoint s3 s2))
