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
module FStar.GSet
(** Computational sets (on Types): membership is a boolean function *)
#set-options "--initial_fuel 0 --max_fuel 0 --initial_ifuel 0 --max_ifuel 0"
open FStar.FunctionalExtensionality
module F = FStar.FunctionalExtensionality

let set (a: Type) : Tot Type = F.restricted_g_t a (fun _ -> bool)

type equal (#a:Type) (s1:set a) (s2:set a) = F.feq_g s1 s2

(* destructors *)
let mem #a x s = s x

(* constructors *)
let empty #a           = F.on_dom_g a (fun x -> false)
let singleton #a x     = F.on_dom_g a #(fun _ -> bool) (fun y -> StrongExcludedMiddle.strong_excluded_middle (y == x))
let union #a s1 s2     = F.on_dom_g a (fun x -> s1 x || s2 x)
let intersect #a s1 s2 = F.on_dom_g a (fun x -> s1 x && s2 x)
let complement #a s    = F.on_dom_g a ( fun x -> not (s x))
let comprehend #a f    = F.on_dom_g a f
let of_set #a f        = F.on_dom_g a (fun x -> Set.mem x f)

(* Properties *)
let mem_empty      #a x       = ()
let mem_singleton  #a x y     = ()
let mem_union      #a x s1 s2 = ()
let mem_intersect  #a x s1 s2 = ()
let mem_complement #a x s     = ()
let mem_subset     #a s1 s2   = ()
let subset_mem     #a s1 s2   = ()
let comprehend_mem #a f x     = ()
let mem_of_set     #a f x     = ()

(* extensionality *)
let lemma_equal_intro #a s1 s2 = ()
let lemma_equal_elim  #a s1 s2 = ()
let lemma_equal_refl  #a s1 s2 = ()
