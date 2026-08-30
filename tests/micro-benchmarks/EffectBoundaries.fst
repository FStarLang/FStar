(*
   Copyright 2008-2025 Microsoft Research

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
module EffectBoundaries

(* `Tot`, `GTot` and `Div` are the primitive effects, and a precondition is a
   trailing implicit `squash` binder rather than part of a computation type.
   This file pins down the boundaries that must still be enforced once the
   specification no longer lives in the comp.

   The cases below that must be rejected are the reason the old design was
   fragile: comparing two arrows used to mean comparing two computation types,
   and it was easy to compare them without their pre/post.  A precondition is
   now a binder, so dropping one is a structural mismatch that no comparison
   can overlook. *)

assume val p : int -> prop

let f (x: int) : Pure int (requires x > 0) (ensures fun r -> r > 0) = x

(* A precondition may not be dropped -- directly, ... *)
[@@expect_failure]
let drop_direct (x: int) : int = f x

(* ... through a let-bound alias, ... *)
[@@expect_failure]
let drop_alias (x: int) : int = let g = f in g x

(* ... by coercing to an unconstrained arrow, ... *)
[@@expect_failure]
let drop_coerce : int -> int = f

(* ... or by passing it where an unconstrained arrow is expected. *)
assume val hof : (int -> int) -> int

[@@expect_failure]
let drop_arg = hof f

(* But it is discharged by a refined binder, by a test, and the postcondition
   is still visible to the caller as a refinement of the result. *)
let use_refined (x: int{x > 0}) : int = f x
let use_test (x: int) : int = if x > 0 then f x else 1
let use_post (x: int{x > 0}) : y: int{y > 0} = f x

(* The same for a lemma, whose precondition is the same binder. *)
assume val lem (x: int) : Lemma (requires x > 0) (ensures p x)

[@@expect_failure]
let drop_lemma_pre (x: int) : Lemma (p x) = lem x

let use_lemma (x: int{x > 0}) : Lemma (p x) = lem x

(* `GTot` is primitive now, so the ghost/total boundary no longer rests on
   `GTot` unfolding to `GHOST`. *)
assume val gv : int -> GTot int

[@@expect_failure]
let ghost_leak (x: int) : Tot int = gv x

[@@expect_failure]
let ghost_leak_arrow : int -> Tot int = gv

let ghost_ok (x: int) : GTot int = gv x

(* and erasure still fires *)
[@@expect_failure]
let reveal_leak (x: Ghost.erased int) : int = Ghost.reveal x

let reveal_ok (x: Ghost.erased int) : GTot int = Ghost.reveal x

(* `Div` likewise. *)
assume val loop : int -> Dv int

[@@expect_failure]
let div_leak (x: int) : Tot int = loop x

let div_ok (x: int) : Dv int = loop x
