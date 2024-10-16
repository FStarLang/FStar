(*
   Copyright 2008-2018 Microsoft Research

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

module FStar.PropositionalExtensionality
(*
 *
 * The propositional extensionality axiom asserts the equality of
 * equisatisfiable propositions.
 *
 * The formulation of this axiom is (clearly) tied closely to the
 * precise definition of `prop`.
 *
 * `Prims.prop` is defined as the type of all subtypes of `unit`,
 * including, e.g., `squash t`, for all `t`.
 *
 * Note, we have considered several other plausible definitions of
 * `prop`, but some of which are actually inconsistent with this
 * axiom.  See, for instance,
 * examples/paradoxes/PropositionalExtensionalityInconsistent.fst.
 *
 *)

assume
val axiom (_:unit)
  : Lemma (forall (p1 p2:prop). (p1 <==> p2) <==> (p1 == p2))

let apply (p1 p2:prop)
  : Lemma (ensures  ((p1 <==> p2) <==> (p1 == p2)))
  = axiom ()
