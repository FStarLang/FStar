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
module Test.CanonMonoid

open FStar.Algebra.Monoid
open FStar.Tactics.V2
open FStar.Tactics.CanonMonoid

let lem0 (a b c d : int) =
  assert (0 + a + b + c + d == (0 + a) + (b + c + 0) + (d + 0)) by (
    canon_monoid int_plus_monoid;
    trefl()
  )

let lem1 (a b c d : nat) =
  assert (0 + a + b + c + d == (0 + a) + (b + c + 0) + (d + 0)) by (
    canon_monoid int_plus_monoid;
    trefl()
  )

let lem2 (a b c d : nat) =
  assert (eq2 #nat (0 + a + b + c + d) ((0 + a) + (b + c + 0) + (d + 0))) by (
    canon_monoid int_plus_monoid;
    trefl()
  )
