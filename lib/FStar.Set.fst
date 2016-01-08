(*--build-config
    other-files:FStar.FunctionalExtensionality.fst FStar.Set.fsi
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
open Prims.PURE

type set (a:Type) = a -> Tot bool

(* destructors *)
let mem x s = s x

(* constructors *)
let empty           = fun _ -> false
let singleton x     = fun y -> y = x
let union s1 s2     = fun x -> s1 x || s2 x
let intersect s1 s2 = fun x -> s1 x && s2 x
let complement s    = fun x -> not (s x)

(* ops *)
let subset s1 s2    = (intersect s1 s2) = s1

(* properties *)
let mem_empty x           = ()
let mem_singleton x y     = ()
let mem_union x s1 s2     = ()
let mem_intersect x s1 s2 = ()
let mem_complement x s    = ()

(* extensionality *)
open FStar.FunctionalExtensionality
type Equal (#a:Type) (s1:set a) (s2:set a) = FEq s1 s2
let lemma_equal_intro s1 s2 = ()
let lemma_equal_elim s1 s2 = ()
let lemma_equal_refl s1 s2 = ()

(* ops *)
let mem_subset s1 s2 =
  cut (Equal (intersect s1 s2) s1)

let subset_mem s1 s2 = ()
