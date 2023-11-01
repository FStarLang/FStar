(*
   Copyright 2023 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.

   Authors: G. Martinez, N. Swamy
*)

module FStar.Sealed

(* This module provides the type ``sealed a`` which is a singleton
   type from the perspective of F*'s logic. I.e., two values `x, y`
   both of type `sealed a` are provably equal.

   However, from the meta-F*, i.e., using the Tac effect, one can
   break the seal and extract an underlying value of type `a` from a
   `sealed a`.

   See also FStar.Sealed.Inhabited for a version of this module for
   use with inhabited types, in a style that is more efficient for
   SMT-based reasoning
*)
assume
new type sealed ([@@@strictly_positive] a : Type u#aa) : Type u#0

(* The main axiom provided by this module:

   Two sealed values of the same type are equal.
   
   Their seal can be broken only at the meta level, by incurring a Tac effect.
   See FStar.Tactics.unseal
*)
val sealed_singl (#a:Type) (x y : sealed a)
  : Lemma (x == y)

(* Sealing a value hides it from the logical fragment of F* *)
val seal (#a : Type u#aa) (x:a) : Tot (sealed a)

val map_seal (#a : Type u#aa) (#b : Type u#bb) (s : sealed a) (f : a -> Tot b) : Tot (sealed b)

val bind_seal (#a : Type u#aa) (#b : Type u#bb) (s : sealed a) (f : a -> Tot (sealed b)) : Tot (sealed b)
