(*
   Copyright 2008-2026 Microsoft Research

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
module RefinementWithSMTPattern

(* A refinement whose formula is a quantifier carrying an SMT pattern that
   mentions [pat], a variable occurring nowhere else in the refinement. The
   SMT encoding abstracts a refinement over its free variables; [pat] must be
   counted among them, or the emitted axiom refers to a constant that is not
   in scope and Z3 rejects the query with "unknown constant". *)
let f (#a: Type) (#pat: (a -> Type)) (#p: (a -> prop))
      (u: (u: unit {forall (x: a). {:pattern (pat x)} p x}))
      (y: a) (_: pat y)
  : Lemma (p y)
  = ()

(* The same shape, but arising from a postcondition rather than a source-level
   refinement: [forall_intro_with_pat] below is checked against a computation
   type whose postcondition carries a pattern. *)
assume
val forall_intro (#a: Type) (#p: (a -> prop)) (f: (x: a -> Lemma (p x)))
  : Lemma (forall (x: a). p x)

val forall_intro_with_pat
      (#a: Type) (#c: (x: a -> Type)) (#p: (x: a -> prop))
      (pat: (x: a -> c x))
      (f: (x: a -> Lemma (p x)))
  : Lemma (forall (x: a). {:pattern (pat x)} p x)
let forall_intro_with_pat #a #c #p pat f = forall_intro #a #p f
