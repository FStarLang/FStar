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
module SquashSubtypingDivergence

module UI = FStar.UInt

(* Now that [Lemma (ensures p)] is [Tot (squash p)], checking a lemma whose
   body is itself a lemma call produces a subtyping problem

     squash <what the body proves>  <:  squash <what the lemma promises>

   Both sides have head [Prims.squash], so the application-congruence rule
   used to fire and demand that the two propositions be *equal*, delta-unfolding
   both of them in search of a syntactic match.  For bitvector propositions
   that unfolding does not terminate: [nth]/[logand]/[shift_right] unfold into
   [to_vec]/[from_vec] recursion and the typechecker allocates until it dies.

   [squash p] is by definition [_:unit{p}], so the relation between the two
   sides is an implication, not an equality.  These lemmas must therefore
   check quickly rather than diverge. *)

let shift_bit_lemma_true (u : UI.uint_t 32) (i : nat{i < 32})
  : Lemma (requires True)
          (ensures UI.nth #32 (UI.shift_right #32 u i `UI.logand` 1) 31
                     == UI.nth #32 u (31 - i))
  = UI.shift_right_lemma_2 u i i;
    UI.logand_definition (UI.shift_right #32 u i) 1 31

(* The same, with no [requires] clause. *)
let shift_bit_lemma_true' (u : UI.uint_t 32) (i : nat{i < 32})
  : Lemma (ensures UI.nth #32 (UI.shift_right #32 u i `UI.logand` 1) 31
                     == UI.nth #32 u (31 - i))
  = UI.shift_right_lemma_2 u i i;
    UI.logand_definition (UI.shift_right #32 u i) 1 31

(* A single lemma call in the body is enough to trigger it. *)
let shift_bit_lemma_one_call (u : UI.uint_t 32) (i : nat{i < 32})
  : Lemma (ensures UI.nth #32 (UI.shift_right #32 u i `UI.logand` 1) 31
                     == UI.nth #32 u (31 - i))
  = UI.shift_right_lemma_2 u i i
