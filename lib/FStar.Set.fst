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
abstract type set (a:Type) = a -> Tot bool

(* Destructors *)
abstract val mem : #a:Type -> a -> set a -> Tot bool

(* Constructors *)
abstract val empty      : #a:Type -> Tot (set a)
abstract val singleton  : #a:Type -> a -> Tot (set a)
abstract val union      : #a:Type -> set a -> set a -> Tot (set a)
abstract val intersect  : #a:Type -> set a -> set a -> Tot (set a)
abstract val complement : #a:Type -> set a -> Tot (set a)

(* destructors *)
let mem x s = s x

(* constructors *)
let empty           = fun _ -> false
let singleton x     = fun y -> y = x
let union s1 s2     = fun x -> s1 x || s2 x
let intersect s1 s2 = fun x -> s1 x && s2 x
let complement s    = fun x -> not (s x)

(* Ops *)
abstract val subset     : #a:Type -> set a -> set a -> Tot bool

(* ops *)
let subset s1 s2    = (intersect s1 s2) = s1

(* Properties *)
abstract val mem_empty: #a:Type -> x:a -> Lemma
   (requires True)
   (ensures (not (mem x empty)))
   [SMTPat (mem x empty)]

abstract val mem_singleton: #a:Type -> x:a -> y:a -> Lemma
   (requires True)
   (ensures (mem y (singleton x) = (x=y)))
   [SMTPat (mem y (singleton x))]

abstract val mem_union: #a:Type -> x:a -> s1:set a -> s2:set a -> Lemma
   (requires True)
   (ensures (mem x (union s1 s2) = (mem x s1 || mem x s2)))
   [SMTPat (mem x (union s1 s2))]

abstract val mem_intersect: #a:Type -> x:a -> s1:set a -> s2:set a -> Lemma
   (requires True)
   (ensures (mem x (intersect s1 s2) = (mem x s1 && mem x s2)))
   [SMTPat (mem x (intersect s1 s2))]

abstract val mem_complement: #a:Type -> x:a -> s:set a -> Lemma
   (requires True)
   (ensures (mem x (complement s) = not(mem x s)))
   [SMTPat (mem x (complement s))]

abstract val mem_subset: #a:Type -> s1:set a -> s2:set a -> Lemma
   (requires (forall x. mem x s1 ==> mem x s2))
   (ensures (subset s1 s2))
   [SMTPat (subset s1 s2)]

abstract val subset_mem: #a:Type -> s1:set a -> s2:set a -> Lemma
   (requires (subset s1 s2))
   (ensures (forall x. mem x s1 ==> mem x s2))
   [SMTPat (subset s1 s2)]

(* properties *)
let mem_empty x           = ()
let mem_singleton x y     = ()
let mem_union x s1 s2     = ()
let mem_intersect x s1 s2 = ()
let mem_complement x s    = ()

(* extensionality *)
open FStar.FunctionalExtensionality
abstract type Equal (#a:Type) (s1:set a) (s2:set a) = FEq s1 s2
abstract val lemma_equal_intro: #a:Type -> s1:set a -> s2:set a -> Lemma
    (requires  (forall x. mem x s1 = mem x s2))
    (ensures (Equal s1 s2))
    [SMTPatT (Equal s1 s2)]

abstract val lemma_equal_elim: #a:Type -> s1:set a -> s2:set a -> Lemma
    (requires (Equal s1 s2))
    (ensures  (s1 = s2))
    [SMTPatT (Equal s1 s2)]

abstract val lemma_equal_refl: #a:Type -> s1:set a -> s2:set a -> Lemma 
    (requires (s1 = s2))
    (ensures  (Equal s1 s2))
    [SMTPatT (Equal s1 s2)]
let lemma_equal_intro s1 s2 = ()
let lemma_equal_elim s1 s2 = ()
let lemma_equal_refl s1 s2 = ()

(* ops *)
let mem_subset s1 s2 =
  cut (Equal (intersect s1 s2) s1)

let subset_mem s1 s2 = ()
