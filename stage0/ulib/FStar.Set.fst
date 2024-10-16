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
(** Computational sets (on eqtypes): membership is a boolean function *)
#set-options "--initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0"
open FStar.FunctionalExtensionality
module F = FStar.FunctionalExtensionality

let set (a:eqtype) = F.restricted_t a (fun _ -> bool)

let equal (#a:eqtype) (s1:set a) (s2:set a) = F.feq s1 s2

(* destructors *)

let mem #a x s = s x

(* constructors *)
let empty #a = F.on_dom a (fun x -> false)
let singleton #a x = F.on_dom a (fun y -> y = x)
let union #a s1 s2 = F.on_dom a (fun x -> s1 x || s2 x)
let intersect #a s1 s2 = F.on_dom a (fun x -> s1 x && s2 x)
let complement #a s = F.on_dom a (fun x -> not (s x))
let intension #a f = F.on_dom a f

(* Properties *)
let mem_empty      #a x       = ()
let mem_singleton  #a x y     = ()
let mem_union      #a x s1 s2 = ()
let mem_intersect  #a x s1 s2 = ()
let mem_complement #a x s     = ()
let mem_intension  #a x f      = ()
let mem_subset     #a s1 s2   = ()
let subset_mem     #a s1 s2   = ()

(* extensionality *)
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
