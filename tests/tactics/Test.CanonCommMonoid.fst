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
module Test.CanonCommMonoid

open FStar.Algebra.CommMonoid
open FStar.Tactics.V2
open FStar.Tactics.CanonCommMonoid
open FStar.Classical

(* let lem2 (a b c d : int) = *)
(*   assert_by_tactic (0 + 1 + a + b + c + d + 2 == (b + 0) + 2 + d + (c + a + 0) + 1) *)
(*   (fun _ -> canon_monoid_special [quote a; quote b] int_plus_cm; *)
(*             dump "this won't work, admitting"; admit1()) *)

(* Trying to do something separation logic like. Want to
//    prove a goal of the form: given some concrete h0 and h1
//    exists h1', h1 * h1' == h0. -- can use apply exists_intro to get an uvar
//    Do this for an arbitrary commutative monoid. *)

let sep_logic
// TODO: this generality makes unfold_def fail with:
//       (Error) Variable "mult#1139342" not found
//       - Guido thinks this is related to
//         https://github.com/FStarLang/FStar/issues/1392
// (a:Type) (m:cm a) (x y z1 z2 z3 : a) = let op_Star = CM?.mult m in
// so working around it for now
(x y z1 z2 z3 : int) = let m = int_multiply_cm in let op_Star = op_Multiply in
  let h0 = z1 * CM?.unit m * (x * z2 * y * CM?.unit m) * z3 in
  let h1 = x * y in
  assert_by_tactic (exists h1'. h1 * h1' == h0)
  (fun _ -> apply_lemma (`exists_intro);
            flip();
            canon_monoid m;
            trefl()
            // this one blows up big time (takes up all RAM)
            // exact (cur_witness())
            // GM, May 8th: This goal is now skipped since its witness was solved already
            (* dismiss() *)
  )

(* TODO: Need better control of reduction:
//          - unfold_def still not good enough, see stopgap above *)

(* TODO: need a version of canon that works on assumption(s)
//          (canon_in / canon_all) *)

(* TODO: Wondering whether we should support arbitrary re-association?
//          Could be useful for separation logic, but we might also just
//          work around it. *)

(* TODO: would be nice to just find all terms of monoid type in the
//          goal and replace them with their canonicalization;
//          basically use flatten_correct instead of monoid_reflect
//          - for this to be efficient need Nik's pointwise' that can
//            stop traversing when finding something interesting
//          - even better, the user would have control over the place(s)
//            where the canonicalization is done *)

(* TODO (open ended) Do the things used for reflective tactics really
//                      need to be this pure? Can we prove correctness of
//                      denotations intrinsically / by monadic
//                      reification for an effectful denotation? *)
