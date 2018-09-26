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
module P = FStar.PropositionalExtensionality
module F = FStar.FunctionalExtensionality

(*
 * AR: mark it must_erase_for_extraction temporarily until CMI comes in
 *)
[@must_erase_for_extraction]
abstract type set (a:Type) =
  f:F.restricted_t a (fun _ -> prop)

abstract type equal (#a:Type) (s1:set a) (s2:set a) = forall x. s1 x <==> s2 x

(* destructors *)

abstract val mem : 'a -> set 'a -> Tot Type0
let mem x s = s x

(* constructors *)
abstract val empty      : #a:Type -> Tot (set a)
abstract val singleton  : #a:Type -> x:a -> Tot (set a)
abstract val union      : #a:Type -> x:set a -> y:set a -> Tot (set a)
abstract val intersect  : #a:Type -> x:set a -> y:set a -> Tot (set a)
abstract val complement : #a:Type -> x:set a -> Tot (set a)

(*
 * AR: 05/12: adding calls to equational lemmas from PropositionalExtensionality
 *            these should go away with proper prop support
 *            also see the comment in PropositionalExtensionality.fst
 *)

let empty #a           = F.on_dom a #(fun _ -> prop) (fun x -> False)
let singleton #a x     = F.on_dom a #(fun _ -> prop) (fun y -> y == x)
let union #a s1 s2     = F.on_dom a #(fun _ -> prop) (fun x -> s1 x \/ s2 x)
let intersect #a s1 s2 = F.on_dom a #(fun _ -> prop) (fun x -> s1 x /\ s2 x)
let complement #a s    = F.on_dom a #(fun _ -> prop) (fun x -> ~ (s x))

(* ops *)
type subset (#a:Type) (s1:set a) (s2:set a) :Type0 = forall x. mem x s1 ==> mem x s2

(* Properties *)
abstract val mem_empty: #a:Type -> x:a -> Lemma
   (requires True)
   (ensures (~ (mem x empty)))
   [SMTPat (mem x empty)]

abstract val mem_singleton: #a:Type -> x:a -> y:a -> Lemma
   (requires True)
   (ensures (mem y (singleton x) <==> (x==y)))
   [SMTPat (mem y (singleton x))]

abstract val mem_union: #a:Type -> x:a -> s1:set a -> s2:set a -> Lemma
   (requires True)
   (ensures (mem x (union s1 s2) == (mem x s1 \/ mem x s2)))
   [SMTPat (mem x (union s1 s2))]

abstract val mem_intersect: #a:Type -> x:a -> s1:set a -> s2:set a -> Lemma
   (requires True)
   (ensures (mem x (intersect s1 s2) == (mem x s1 /\ mem x s2)))
   [SMTPat (mem x (intersect s1 s2))]

abstract val mem_complement: #a:Type -> x:a -> s:set a -> Lemma
   (requires True)
   (ensures (mem x (complement s) == ~(mem x s)))
   [SMTPat (mem x (complement s))]

abstract val mem_subset: #a:Type -> s1:set a -> s2:set a -> Lemma
   (requires (forall x. mem x s1 ==> mem x s2))
   (ensures (subset s1 s2))
   [SMTPat (subset s1 s2)]

abstract val subset_mem: #a:Type -> s1:set a -> s2:set a -> Lemma
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

abstract val lemma_equal_intro: #a:Type -> s1:set a -> s2:set a -> Lemma
    (requires  (forall x. mem x s1 <==> mem x s2))
    (ensures (equal s1 s2))
    [SMTPat (equal s1 s2)]

abstract val lemma_equal_elim: #a:Type -> s1:set a -> s2:set a -> Lemma
    (requires (equal s1 s2))
    (ensures  (s1 == s2))
    [SMTPat (equal s1 s2)]

abstract val lemma_equal_refl: #a:Type -> s1:set a -> s2:set a -> Lemma
    (requires (s1 == s2))
    (ensures  (equal s1 s2))
    [SMTPat (equal s1 s2)]

let lemma_equal_intro #a s1 s2 = ()
let lemma_equal_elim  #a s1 s2 = PredicateExtensionality.predicateExtensionality a s1 s2
let lemma_equal_refl  #a s1 s2 = ()

abstract let tset_of_set (#a:eqtype) (s:Set.set a) :set a =
  F.on_dom a #(fun _ -> prop) (fun (x:a) -> squash (b2t (Set.mem x s)))

private let lemma_mem_tset_of_set_l (#a:eqtype) (s:Set.set a) (x:a)
  :Lemma (requires True)
         (ensures (mem x (tset_of_set s) ==> Set.mem x s))
  = if FStar.StrongExcludedMiddle.strong_excluded_middle (mem x (tset_of_set s)) then
      let t1 = mem x (tset_of_set s) in
      let t2 = b2t (Set.mem x s) in
      let u:(squash t1) = FStar.Squash.get_proof t1 in
      let u:(squash (squash t2)) = u in
      let u:squash t2 = FStar.Squash.join_squash u in
      FStar.Squash.give_proof u
    else ()

private let lemma_mem_tset_of_set_r (#a:eqtype) (s:Set.set a) (x:a)
  :Lemma (requires True)
         (ensures (Set.mem x s ==> mem x (tset_of_set s)))
  = if Set.mem x s then
      let u:squash (b2t (Set.mem x s)) = () in
      let _ = assert (mem x (tset_of_set s) == squash (b2t (Set.mem x s))) in
      FStar.Squash.give_proof u
    else ()

let lemma_mem_tset_of_set (#a:eqtype) (s:Set.set a) (x:a)
  :Lemma (requires True)
         (ensures  (Set.mem x s <==> mem x (tset_of_set s)))
         [SMTPat (mem x (tset_of_set s))]
  = lemma_mem_tset_of_set_l #a s x; lemma_mem_tset_of_set_r #a s x

abstract
let filter (#a:Type) (f:a -> Type0) (s:set a) : set a =
  F.on_dom a #(fun _ -> prop) (fun (x:a) -> f x /\ s x)

let lemma_mem_filter (#a:Type) (f:(a -> Type0)) (s:set a) (x:a)
  :Lemma (requires True)
         (ensures  (mem x (filter f s) <==> mem x s /\ f x))
         [SMTPat (mem x (filter f s))]
  = ()

let exists_y_in_s (#a:Type) (#b:Type) (s:set a) (f:a -> Tot b) (x:b) : Tot prop =
  exists (y:a). mem y s /\ x == f y

abstract
let map (#a:Type) (#b:Type) (f:a -> Tot b) (s:set a) : Tot (set b) =
  F.on_dom b (exists_y_in_s s f)

let lemma_mem_map (#a:Type) (#b:Type) (f:(a -> Tot b)) (s:set a) (x:b)
  :Lemma ((exists (y:a). {:pattern (mem y s)} mem y s /\ x == f y) <==> mem x (map f s))
         [SMTPat (mem x (map f s))]
  = ()

#reset-options
val as_set': #a:Type -> list a -> Tot (set a)
let rec as_set' #a l =
  match l with
  | [] -> empty
  | hd::tl -> union (singleton hd) (as_set' tl)


(* unfold let as_set (#a:Type) (l:list a) : set a = *)
(*   Prims.norm [zeta; iota; delta_only ["FStar.TSet.as_set'"]] (as_set' l) *)
