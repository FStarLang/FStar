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
module FStar.RealLiteral

(* Note: this module deliberately depends on nothing but Prims, since it is
referenced by the (very low-level) reflection API. Parsing a literal from a
string is in FStar.RealLiteral.Parse. *)

(** A parsed representation of a real (decimal) literal, denoting the exact
rational number [mantissa * 10^exponent].

This type is used by the F* compiler for the real constants appearing in
terms (see [FStarC.Const.Const_real]), and is also the payload of the
[C_Real] case of the reflection API's [vconst] type. Note that this is not
the type of *reals* ([FStar.Real.real]): it is the type of the literals
denoting them.

The representation is canonical (see [canonical] below): two literals denote
the same real number if and only if they are equal. Hence [=] on this type
is (decidable) equality of the denoted real numbers. This is essential for
soundness: the F* normalizer and the SMT solver both consider two real
constants to be equal exactly when they denote the same number. *)

[@@ FStar.Attributes.PpxDerivingYoJson; FStar.Attributes.PpxDerivingShow]
type real_literal_repr = {
  mantissa : int;
  exponent : int;
}

(** A literal is canonical when it uses no more decimal places than needed:
either it denotes an integer, and then the exponent is 0, or the last
digit of the mantissa is non-zero. Every real number denoted by some
literal is denoted by exactly one canonical literal. *)
let canonical (r : real_literal_repr) : bool =
  r.exponent = 0 || (r.exponent < 0 && r.mantissa % 10 <> 0)

[@@ FStar.Attributes.PpxDerivingYoJson; FStar.Attributes.PpxDerivingShow]
type real_literal = r:real_literal_repr{canonical r}

private let rec pow10 (n : nat) : Tot pos = if n = 0 then 1 else 10 * pow10 (n-1)

(* Drops the trailing zeros of the mantissa, adjusting the exponent, so
that the result is canonical. *)
private let rec strip (m : int) (e : int{e <= 0}) : Tot real_literal (decreases (-e)) =
  if e = 0 || m % 10 <> 0
  then { mantissa = m; exponent = e }
  else strip (m / 10) (e + 1)

(** The literal denoting [mantissa * 10^exponent], canonicalized. *)
let mk (m e : int) : real_literal =
  if e >= 0
  then { mantissa = m * pow10 e; exponent = 0 }
  else strip m e

(** The literal denoting the integer [i], exactly. *)
let of_int (i : int) : real_literal = { mantissa = i; exponent = 0 }

(* The number of decimal digits of [x]. *)
private let rec ndigits (x : nat) : Tot nat (decreases x) =
  if x < 10 then 1 else 1 + ndigits (x / 10)

(* Prepends [n] zeros to [s]. *)
private let rec zeros (n : nat) (s : string) : Tot string (decreases n) =
  if n = 0 then s else zeros (n-1) ("0" ^ s)

(** A decimal representation of the literal, e.g. "0.5", "-1.5", "10.0".
The result always contains a '.', and is always accepted by
[FStar.RealLiteral.Parse.of_string], roundtripping to the same literal. *)
let to_string (r : real_literal) : string =
  let m = if r.mantissa < 0 then - r.mantissa else r.mantissa in
  let k : nat = - r.exponent in
  let p = pow10 k in
  let fpart = m % p in
  (* [fpart] must be printed with exactly [k] digits, zero-padded. *)
  let pad = if ndigits fpart >= k then 0 else k - ndigits fpart in
  (if r.mantissa < 0 then "-" else "")
    ^ string_of_int (m / p)
    ^ "."
    ^ (if k = 0 then "0" else zeros pad (string_of_int fpart))

(** Compares the numbers denoted by two literals, returning a negative
integer, zero, or a positive integer when the first is respectively
smaller than, equal to, or greater than the second. *)
let compare (r1 r2 : real_literal) : int =
  (* Scale both mantissas to the smaller of the two exponents. *)
  let e = if r1.exponent <= r2.exponent then r1.exponent else r2.exponent in
  let m1 = r1.mantissa * pow10 (r1.exponent - e) in
  let m2 = r2.mantissa * pow10 (r2.exponent - e) in
  if m1 < m2 then -1 else if m1 = m2 then 0 else 1
