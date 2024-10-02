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
[@@erasable]
let set a = F.restricted_t a (fun _ -> prop)

let equal #_ s1 s2 = forall x. s1 x <==> s2 x

let mem x s = s x

let empty #a           = F.on_dom a #(fun _ -> prop) (fun x -> False)
let singleton #a x     = F.on_dom a #(fun _ -> prop) (fun y -> y == x)
let union #a s1 s2     = F.on_dom a #(fun _ -> prop) (fun x -> s1 x \/ s2 x)
let intersect #a s1 s2 = F.on_dom a #(fun _ -> prop) (fun x -> s1 x /\ s2 x)
let complement #a s    = F.on_dom a #(fun _ -> prop) (fun x -> ~ (s x))
let intension #a f     = F.on_dom a #(fun _ -> prop) f

let mem_empty      #_ _     = ()
let mem_singleton  #_ _ _   = ()
let mem_union      #_ _ _ _ = ()
let mem_intersect  #_ _ _ _ = ()
let mem_complement #_ _ _   = ()
let mem_subset     #_ _ _   = ()
let subset_mem     #_ _ _   = ()
let mem_intension  #_ _ _   = ()

let lemma_equal_intro #_ _ _   = ()
let lemma_equal_elim  #a s1 s2 = PredicateExtensionality.predicateExtensionality a s1 s2
let lemma_equal_refl  #_ _ _   = ()

let tset_of_set #a s =
  F.on_dom a #(fun _ -> prop) (fun (x:a) -> squash (b2t (Set.mem x s)))

#push-options "--smtencoding.valid_intro true --smtencoding.valid_elim true"
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
#pop-options

private let lemma_mem_tset_of_set_r (#a:eqtype) (s:Set.set a) (x:a)
  :Lemma (requires True)
         (ensures (Set.mem x s ==> mem x (tset_of_set s)))
  = if Set.mem x s then
      let u:squash (b2t (Set.mem x s)) = () in
      let _ = assert (mem x (tset_of_set s) == squash (b2t (Set.mem x s))) in
      FStar.Squash.give_proof u
    else ()

let lemma_mem_tset_of_set #a s x = lemma_mem_tset_of_set_l #a s x; lemma_mem_tset_of_set_r #a s x

let filter #a f s = F.on_dom a #(fun _ -> prop) (fun (x:a) -> f x /\ s x)

let lemma_mem_filter #a f s x = ()

let exists_y_in_s (#a:Type) (#b:Type) (s:set a) (f:a -> Tot b) (x:b) : Tot prop =
  exists (y:a). mem y s /\ x == f y

let map #_ #b f s = F.on_dom b (exists_y_in_s s f)

let lemma_mem_map #_ #_ _ _ _ = ()
