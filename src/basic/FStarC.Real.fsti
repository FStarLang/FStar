(*
   Copyright 2017-2024 Microsoft Research

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
module FStarC.Real

open FStarC.Effect
open FStarC.Order

module RL = FStar.RealLiteral

(* A type for embedded real constants. This allows to write embeddings for them
(see FStarC.Syntax.Embeddings and FStarC.TypeChecker.NBETerm).

A real constant denotes the exact rational number [mantissa * 10^exponent].
Note that this is a *parsed* representation: it is impossible to construct
a real constant that is not a well-formed number, which matters since these
constants end up in the SMT queries we generate.

This is exactly the type of real literals in the reflection API (the payload
of [FStar.Stubs.Reflection.V2.Data.C_Real]), so that a constant in a term and
a constant in a term view are literally the same thing.

The representation is canonical: two reals are equal (structurally, hence
also for [=] and for hashing) if and only if they denote the same number. *)
[@@ PpxDerivingYoJson; PpxDerivingShow]
type real = RL.real_literal

(* The mantissa and exponent of a real, i.e. [r] denotes [mantissa r * 10^exponent r]. *)
val mantissa (r : real) : int
val exponent (r : real) : int

(* The real [mantissa * 10^exponent], canonicalized. *)
val mk (mantissa exponent : int) : real

(* Like [mk], but returns None if the given pair is not already the canonical
representation of that real. Use this instead of [mk] when reading a real out
of a term (see [e_real_literal] in FStarC.Syntax.Embeddings): silently
canonicalizing there would make unembedding non-injective. *)
val try_mk (mantissa exponent : int) : option real

(* The real number [i], exactly. *)
val of_int (i : int) : real

(* Parse a real literal. The accepted syntax is an optional '-' sign,
followed by a non-empty sequence of decimal digits, optionally followed by
a '.' and a (possibly empty) sequence of decimal digits. Returns None if
the string is not a well-formed real literal. *)
val of_string (s : string) : option real

(* A canonical decimal representation of the real, e.g. "0.5", "-1.5",
"10.0". The result always contains a '.', and is always accepted by
of_string (roundtripping to the same real). *)
val to_string (r : real) : string

(* Like to_string, but valid SMT-LIB 2 syntax for a Real term:
negative reals are printed as an application of unary minus. *)
val to_smt_string (r : real) : string

(* Compares two reals. *)
val cmp (r1 r2 : real) : order
