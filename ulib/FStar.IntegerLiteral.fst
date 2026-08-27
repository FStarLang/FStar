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
module FStar.IntegerLiteral

(* Note: this module deliberately depends on nothing but Prims, since it is
referenced both by the F* compiler's constant type ([FStarC.Const]) and by
the (very low-level) reflection API ([FStar.Stubs.Reflection.V2.Data]). Both
of those modules [include] this one, so its types are shared between the
compiler and userland, and its constructors remain accessible under their
names. *)

(** The base in which an integer literal was written in the source program.

This is *presentational metadata only*: it plays no role in the meaning of a
literal, which is fully determined by its (mathematical) integer value. It is
recorded so that pretty-printing and code extraction can echo the literal back
in the base the user wrote it in.

Because it is not semantically relevant, the reflection API exposes it
*sealed* (see [FStar.Stubs.Reflection.V2.Data.vconst]). This is essential for
soundness: the F* normalizer, the SMT solver and the extraction pipeline all
consider two integer constants to be equal exactly when they denote the same
number (see [FStarC.Const.eq_const]), so a metaprogram must not be able to
distinguish [0x10] from [16]. *)
[@@ FStar.Attributes.PpxDerivingYoJson; FStar.Attributes.PpxDerivingShow]
type int_base =
  | Dec  (* e.g. 16    *)
  | Hex  (* e.g. 0x10  *)
  | Oct  (* e.g. 0o20  *)
  | Bin  (* e.g. 0b10000 *)
