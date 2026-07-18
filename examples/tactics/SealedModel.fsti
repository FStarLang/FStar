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

module SealedModel

open FStar.Tactics.Effect

(* This module provides a model for the `FStar.Sealed.sealed` type
   in ulib, by implementing its interface over a single axiom
   about Tac functions. This is not done directly in ulib/
   due to some circular dependencies that would be introduced if
   we tried to use the Tac effect from the FStar.Sealed module,
   so it is just kept here in examples.

   See also FStar.Sealed.fsti in the library.
*)

new
val sealed ([@@@strictly_positive] a : Type u#aa) : Type u#0

(* The main axiom provided by this module:

   Two sealed values of the same type are equal.

   Their seal can be broken only at the meta level, by incurring a Tac effect.
   See FStar.Tactics.unseal
*)
val sealed_singl (#a:Type) (x y : sealed a)
  : Lemma (x == y)

(* Sealing a value hides it from the logical fragment of F* *)
val seal (#a : Type u#aa) (x:a) : Tot (sealed a)

(* Unsealing, a Tac function. In particular a TacS, it never raises an exception. *)
val unseal (#a : Type u#aa) (s : sealed a) : TacS a

(* (Tac) functions can be mapped inside of a seal, without incurring
in an effect. *)
val map_seal
  (#a : Type u#aa) (b : Type u#bb)
  (s : sealed a)
  (f : a -> TacS b)
: Tot (sealed b)

(* Similarly to above, we can do a pure bind. *)
val bind_seal
  (#a : Type u#aa) (b : Type u#bb)
  (s : sealed a)
  (f : a -> TacS (sealed b))
: Tot (sealed b)
