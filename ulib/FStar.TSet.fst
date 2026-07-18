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

module F = FStar.FunctionalExtensionality

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
  F.on_dom a #(fun _ -> prop) fun (x:a) -> Set.mem x s

let lemma_mem_tset_of_set #a s x = ()

let filter #a f s = F.on_dom a #(fun _ -> prop) (fun (x:a) -> f x /\ s x)

let lemma_mem_filter #a f s x = ()

let exists_y_in_s (#a:Type) (#b:Type) (s:set a) (f:a -> Tot b) (x:b) : Tot prop =
  exists (y:a). mem y s /\ x == f y

let map #_ #b f s = F.on_dom b (exists_y_in_s s f)

let lemma_mem_map #_ #_ _ _ _ = ()
