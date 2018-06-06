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

type cmp_t (a:Type) = a -> a -> prop
unfold let default_cmp (a:Type) :cmp_t a = fun (x y:a) -> x == y

abstract type set_cmp (a:Type) (cmp:cmp_t a) = a -> Tot prop
type set (a:Type) = set_cmp a (default_cmp a)

abstract type equal_cmp (#a:Type) (#cmp:cmp_t a) (s1 s2:set_cmp a cmp) = forall (x:a). s1 x <==> s2 x
type equal (#a:Type) (s1 s2:set a) = equal_cmp s1 s2

(* destructors *)

abstract let mem_cmp (#a:Type) (#cmp:cmp_t a) (x:a) (s:set_cmp a cmp) :Type0 = s x
let mem (#a:Type) (x:a) (s:set a) = mem_cmp x s

abstract let empty_cmp (#a:Type) (#cmp:cmp_t a) :set_cmp a cmp = fun (x:a) -> False
let empty (#a:Type) :set a = empty_cmp

abstract let singleton_cmp (#a:Type) (#cmp:cmp_t a) (x:a) :set_cmp a cmp = fun (y:a) -> cmp x y
let singleton (#a:Type) (x:a) :set a = singleton_cmp x

abstract let union_cmp (#a:Type) (#cmp:cmp_t a) (s1 s2:set_cmp a cmp) :set_cmp a cmp = fun (x:a) -> s1 x \/ s2 x
let union (#a:Type) (s1 s2:set a) :set a = union_cmp s1 s2

abstract let intersect_cmp (#a:Type) (#cmp:cmp_t a) (s1 s2:set_cmp a cmp) :set_cmp a cmp = fun (x:a) -> s1 x /\ s2 x
let intersect (#a:Type) (s1 s2:set a) :set a = intersect_cmp s1 s2

abstract let complement_cmp (#a:Type) (#cmp:cmp_t a) (s:set_cmp a cmp) :set_cmp a cmp = fun (x:a) -> ~ (s x)
let complement (#a:Type) (s:set a) :set a = complement_cmp s

(* ops *)
type subset_cmp (#a:Type) (#cmp:cmp_t a) (s1 s2:set_cmp a cmp) :Type0 = forall (x:a). mem_cmp x s1 ==> mem_cmp x s2
type subset (#a:Type) (s1 s2:set a) :Type0 = subset_cmp s1 s2

let lemma_mem_empty (#a:Type) (#cmp:cmp_t a) (x:a)
  :Lemma (requires True) (ensures (~ (mem_cmp x (empty_cmp #a #cmp))))
         [SMTPat (mem_cmp x (empty_cmp #a #cmp))]
  = ()

let lemma_mem_singleton (#a:Type) (#cmp:cmp_t a) (x y:a)
  :Lemma (requires True) (ensures (mem_cmp y (singleton_cmp #a #cmp x) <==> cmp x y))
         [SMTPat (mem_cmp y (singleton_cmp #a #cmp x))]
  = ()

let lemma_mem_union (#a:Type) (#cmp:cmp_t a) (x:a) (s1 s2:set_cmp a cmp)
  :Lemma (requires True) (ensures (mem_cmp x (union_cmp s1 s2) == (mem_cmp x s1 \/ mem_cmp x s2)))
   [SMTPat (mem_cmp x (union_cmp s1 s2))]
  = ()

let lemma_mem_intersect (#a:Type) (#cmp:cmp_t a) (x:a) (s1 s2:set_cmp a cmp)
  :Lemma (requires True) (ensures (mem_cmp x (intersect_cmp s1 s2) == (mem_cmp x s1 /\ mem_cmp x s2)))
   [SMTPat (mem_cmp x (intersect_cmp s1 s2))]
  = ()
  
let lemma_mem_complement (#a:Type) (#cmp:cmp_t a) (x:a) (s:set_cmp a cmp)
  :Lemma (requires True) (ensures (mem_cmp x (complement_cmp s) == ~ (mem_cmp x s)))
   [SMTPat (mem_cmp x (complement_cmp s))]
  = ()

let lemma_mem_subset (#a:Type) (#cmp:cmp_t a) (s1 s2:set_cmp a cmp)
  :Lemma (requires (forall x. mem_cmp x s1 ==> mem_cmp x s2)) (ensures (subset_cmp s1 s2))
   [SMTPat (subset_cmp s1 s2)]
  = ()

let lemma_subset_mem (#a:Type) (#cmp:cmp_t a) (s1 s2:set_cmp a cmp)
  :Lemma (requires (subset_cmp s1 s2)) (ensures (forall x. mem_cmp x s1 ==> mem_cmp x s2))
   [SMTPat (subset_cmp s1 s2)]
  = ()

(* extensionality *)

let lemma_equal_intro (#a:Type) (#cmp:cmp_t a) (s1 s2:set_cmp a cmp)
  :Lemma (requires  (forall x. mem_cmp x s1 <==> mem_cmp x s2)) (ensures (equal_cmp s1 s2))
   [SMTPat (equal_cmp s1 s2)]
  = ()

let lemma_equal_elim (#a:Type) (#cmp:cmp_t a) (s1 s2:set_cmp a cmp)
  :Lemma (requires (equal_cmp s1 s2)) (ensures  (s1 == s2))
   [SMTPat (equal_cmp s1 s2)]
  = PredicateExtensionality.predicateExtensionality a s1 s2

let lemma_equal_refl (#a:Type) (#cmp:cmp_t a) (s1 s2:set_cmp a cmp)
  :Lemma (requires (s1 == s2)) (ensures  (equal_cmp s1 s2))
   [SMTPat (equal_cmp s1 s2)]
  = ()

abstract let tset_of_set (#a:eqtype) (s:Set.set a) :set a =
  fun (x:a) -> squash (b2t (Set.mem x s))

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
let filter_cmp (#a:Type) (#cmp:cmp_t a) (f:a -> Type0) (s:set_cmp a cmp) :set_cmp a cmp =
  fun (x:a) -> f x /\ s x
let filter (#a:Type) (f:a -> Type0) (s:set a) :set a = filter_cmp f s

let lemma_mem_filter (#a:Type) (#cmp:cmp_t a) (f:(a -> Type0)) (s:set_cmp a cmp) (x:a)
  :Lemma (requires True)
         (ensures  (mem_cmp x (filter_cmp f s) <==> mem_cmp x s /\ f x))
         [SMTPat (mem_cmp x (filter_cmp f s))]
  = ()

let exists_y_in_s (#a:Type) (#b:Type) (#cmp:cmp_t a) (s:set_cmp a cmp) (f:a -> Tot b) (x:b) :Tot prop =
 exists (y:a). mem_cmp y s /\ x == f y

abstract
let map_cmp (#a:Type) (#b:Type) (#cmp:cmp_t a) (f:a -> Tot b) (s:set_cmp a cmp) :Tot (set b) = exists_y_in_s s f
let map (#a:Type) (#b:Type) (f:a -> Tot b) (s:set a) :Tot (set b) = map_cmp f s

let lemma_mem_map (#a:Type) (#b:Type) (#cmp:cmp_t a) (f:(a -> Tot b)) (s:set_cmp a cmp) (x:b)
  :Lemma ((exists (y:a). {:pattern (mem_cmp y s)} mem_cmp y s /\ x == f y) <==> mem_cmp x (map_cmp f s))
         [SMTPat (mem_cmp x (map_cmp f s))]
  = ()

#reset-options
val as_set': #a:Type -> list a -> Tot (set a)
let rec as_set' #a l =
  match l with
  | [] -> empty
  | hd::tl -> union (singleton hd) (as_set' tl)


(* unfold let as_set (#a:Type) (l:list a) : set a = *)
(*   Prims.norm [zeta; iota; delta_only ["FStar.TSet.as_set'"]] (as_set' l) *)
