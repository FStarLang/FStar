(*--build-config
    other-files:ext.fst FStar.Set.fsi
  --*)
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
open FStar.FunctionalExtensionality

(* abstract *) type set (a:Type0) = a -> Tot bool
(* abstract *) type Equal (#a:Type0) (s1:set a) (s2:set a) = FEq s1 s2

(* destructors *)

(* abstract *) val mem : 'a -> set 'a -> Tot bool
let mem x s = s x

(* constructors *)
(* abstract *) val empty      : #a:Type -> Tot (set a)
(* abstract *) val singleton  : 'a -> Tot (set 'a)
(* abstract *) val union      : set 'a -> set 'a -> Tot (set 'a)
(* abstract *) val intersect  : set 'a -> set 'a -> Tot (set 'a)
(* abstract *) val complement : set 'a -> Tot (set 'a)


let empty           = fun #a x -> false
let singleton x     = fun y -> y = x
let union s1 s2     = fun x -> s1 x || s2 x
let intersect s1 s2 = fun x -> s1 x && s2 x
let complement s    = fun x -> not (s x)

(* ops *)
(* abstract *) val subset       : set 'a -> set 'a -> Tot bool
let subset s1 s2 = (intersect s1 s2) = s1

(* Properties *)
(* abstract *) val mem_empty: #a:Type -> x:a -> Lemma
   (requires True)
   (ensures (not (mem x empty)))
   [SMTPat (mem x empty)]

(* abstract *) val mem_singleton: #a:Type -> x:a -> y:a -> Lemma
   (requires True)
   (ensures (mem y (singleton x) = (x=y)))
   [SMTPat (mem y (singleton x))]

(* abstract *) val mem_union: #a:Type -> x:a -> s1:set a -> s2:set a -> Lemma
   (requires True)
   (ensures (mem x (union s1 s2) = (mem x s1 || mem x s2)))
   [SMTPat (mem x (union s1 s2))]

(* abstract *) val mem_intersect: #a:Type -> x:a -> s1:set a -> s2:set a -> Lemma
   (requires True)
   (ensures (mem x (intersect s1 s2) = (mem x s1 && mem x s2)))
   [SMTPat (mem x (intersect s1 s2))]

(* abstract *) val mem_complement: #a:Type -> x:a -> s:set a -> Lemma
   (requires True)
   (ensures (mem x (complement s) = not(mem x s)))
   [SMTPat (mem x (complement s))]

(* abstract *) val mem_subset: #a:Type -> s1:set a -> s2:set a -> Lemma
   (requires (forall x. mem x s1 ==> mem x s2))
   (ensures (subset s1 s2))
   [SMTPat (subset s1 s2)]

(* abstract *) val subset_mem: #a:Type -> s1:set a -> s2:set a -> Lemma
   (requires (subset s1 s2))
   (ensures (forall x. mem x s1 ==> mem x s2))
   [SMTPat (subset s1 s2)]

let mem_empty      #a x       = ()
let mem_singleton  #a x y     = ()
let mem_union      #a x s1 s2 = ()
let mem_intersect  #a x s1 s2 = ()
let mem_complement #a x s     = ()
let subset_mem     #a s1 s2   = ()
let mem_subset     #a s1 s2   = cut (Equal (intersect s1 s2) s1)

(* extensionality *)

(* abstract *) val lemma_equal_intro: #a:Type -> s1:set a -> s2:set a -> Lemma
    (requires  (forall x. mem x s1 = mem x s2))
    (ensures (Equal s1 s2))
    [SMTPatT (Equal s1 s2)]

(* abstract *) val lemma_equal_elim: #a:Type -> s1:set a -> s2:set a -> Lemma
    (requires (Equal s1 s2))
    (ensures  (s1 = s2))
    [SMTPatT (Equal s1 s2)]

(* abstract *) val lemma_equal_refl: #a:Type -> s1:set a -> s2:set a -> Lemma 
    (requires (s1 = s2))
    (ensures  (Equal s1 s2))
    [SMTPatT (Equal s1 s2)]

let lemma_equal_intro #a s1 s2 = ()
let lemma_equal_elim  #a s1 s2 = ()
let lemma_equal_refl  #a s1 s2 = ()

