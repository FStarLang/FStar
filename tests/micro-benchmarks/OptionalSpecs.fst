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
module OptionalSpecs

(* Both the requires and the ensures clause of a computation type are
   optional; a missing one defaults to [True]. *)

let both (x:nat) : Pure nat (requires x > 0) (ensures fun y -> y > 0) = x
let only_pre (x:nat) : Pure nat (requires x > 0) = x
let only_post (x:nat) : Pure nat (ensures fun y -> y >= 0) = x
let neither (x:nat) : Pure nat = x

(* The clauses may also be given positionally. *)
let positional (x:nat) : Pure nat (x > 0) (fun y -> y > 0) = x

let _ = assert (only_pre 1 >= 0)
let _ = assert (only_post 1 >= 0)

(* The same holds for the other effects, and for effect abbreviations. *)
let div_pre (x:nat) : Div nat (requires x > 0) = x
let div_post (x:nat) : Div nat (ensures fun y -> y >= 0) = x

effect MyPure (a:Type) = PURE a
let abbrev_pre (x:nat) : MyPure nat (requires x > 0) = x
let abbrev_post (x:nat) : MyPure nat (ensures fun y -> y >= 0) = x

let ghost_pre (x:nat) : Ghost nat (requires x > 0) = x
let ghost_post (x:nat) : Ghost nat (ensures fun y -> y >= 0) = x

(* Lemma, which has its own desugaring, supports all the combinations too,
   in any order with respect to [decreases] and [SMTPat]. *)
let lemma_both (x:nat) : Lemma (requires x > 0) (ensures x >= 1) = ()
let lemma_pre (x:nat) : Lemma (requires x > 0) = ()
let lemma_post (x:nat) : Lemma (ensures x >= 0) = ()
let lemma_positional (x:nat) : Lemma (x >= 0) = ()
let lemma_pre_pat (x:nat) : Lemma (requires x > 0) [SMTPat (x + 0)] = ()
let lemma_pre_dec (x:nat) : Lemma (requires x > 0) (decreases x) = ()
let lemma_dec_pre (x:nat) : Lemma (decreases x) (requires x > 0) = ()

(* A [Lemma] must still mention at least one of the two clauses. *)
[@@expect_failure [103]]
let lemma_neither (x:nat) : Lemma = ()

[@@expect_failure [103]]
let lemma_only_pat (x:nat) : Lemma [SMTPat (x + 0)] = ()

[@@expect_failure [103]]
let lemma_only_dec (x:nat) : Lemma (decreases x) = ()

[@@expect_failure [103]]
let lemma_two_pres (x:nat) : Lemma (requires x > 0) (requires x > 1) = ()

[@@expect_failure [103]]
let lemma_two_posts (x:nat) : Lemma (ensures x >= 0) (x >= 0) = ()

(* [Tot] and [GTot] are just the pure and ghost effects with an empty
   specification, so they accept [requires] and [ensures] clauses exactly as
   [Pure] and [Ghost] do. *)
let tot_pre (x:nat) : Tot nat (requires x > 0) = x
let tot_post (x:nat) : Tot nat (ensures fun y -> y >= 0) = x
let gtot_pre (x:nat) : GTot nat (requires x > 0) = x
let gtot_post (x:nat) : GTot nat (ensures fun y -> y >= 0) = x

let _ = assert (tot_pre 1 >= 0)

(* And such a postcondition is checked, not ignored. *)
[@@expect_failure [19]]
let tot_bad_post (x:nat) : Tot nat (ensures fun y -> y > x) = x
