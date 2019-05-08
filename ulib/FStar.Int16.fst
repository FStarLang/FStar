(*
   Copyright 2008-2019 Microsoft Research

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
module FStar.Int16
(* This module generated automatically using [mk_int.sh] *)

unfold let n = 16

open FStar.Int
open FStar.Mul

(* NOTE: anything that you fix/update here should be reflected in [FStar.UIntN.fstp], which is mostly
 * a copy-paste of this module. *)

private
type t' =
  | Mk: v:int_t n -> t'

let t : eqtype = t'

unfold
let tt (_:t) = True

[@unfold_for_smt]
let v (a:t)
  : Tot (int_t n)
  = a.v

[@unfold_for_smt]
let int_to_t (a:int_t n)
  : Tot t
  = Mk a

[@unfold_for_smt]
let add (a b:t)
  : Pure t
    (requires size (v a + v b) n)
    (ensures tt)
  = Mk (add (v a) (v b))

(* Subtraction primitives *)
[@unfold_for_smt]
let sub (a b:t)
  : Pure t
    (requires size (v a - v b) n)
    (ensures tt)
  = Mk (sub (v a) (v b))

(* Multiplication primitives *)
[@unfold_for_smt]
let mul (a b:t)
  : Pure t
    (requires size (v a * v b) n)
    (ensures tt)
  = Mk (mul (v a) (v b))

(* Division primitives *)
[@unfold_for_smt]
let div (a b:t)
  : Pure t
    (requires
      v b <> 0 /\
      size (v a / v b) n)  // division overflows on INT_MIN / -1
    (ensures tt)
  = Mk (div (v a) (v b))

(* Modulo primitives *)
(* If a/b is not representable the result of a%b is undefind *)
[@unfold_for_smt]
let rem (a b:t)
  : Pure t
    (requires
      v b <> 0 /\
      size (v a / v b) n)
    (ensures tt)
  = Mk (mod (v a) (v b))

(* Bitwise operators *)
[@unfold_for_smt]
let logand (a b:t)
  : Tot t
  = Mk (logand (v a) (v b))

[@unfold_for_smt]
let logxor (a b:t)
  : Tot t
  = Mk (logxor (v a) (v b))

[@unfold_for_smt]
let logor (a b:t)
  : Tot t
  = Mk (logor (v a) (v b))

[@unfold_for_smt]
let lognot (a:t)
  : Tot t
  = Mk (lognot (v a))

(* Shift operators *)

(** If a is negative the result is implementation defined *)
[@unfold_for_smt]
let shift_right (a:t) (s:UInt32.t)
  : Pure t
    (requires
      0 <= v a /\
      UInt32.v s < n)
    (ensures tt)
  = Mk (shift_right (v a) (UInt32.v s))

(** If a is negative the result is undefined behaviour *)
[@unfold_for_smt]
let shift_left (a:t) (s:UInt32.t)
  : Pure t
    (requires
      0 <= v a /\
      UInt32.v s < n)
    (ensures tt)
  = Mk (shift_left (v a) (UInt32.v s))

(* Comparison operators *)
[@unfold_for_smt]
let eq (a b:t)
  : Tot bool
  = a = b

[@unfold_for_smt]
let gt (a b:t)
  : Tot bool
  = gt #n (v a) (v b)

[@unfold_for_smt]
let gte (a b:t)
  : Tot bool
  = gte #n (v a) (v b)

[@unfold_for_smt]
let lt (a b:t)
  : Tot bool
  = lt #n (v a) (v b)

[@unfold_for_smt]
let lte (a b:t)
  : Tot bool
  = lte #n (v a) (v b)

(* Infix notations *)
unfold let (  +^ ) = add
unfold let (  -^ ) = sub
unfold let (  *^ ) = mul
unfold let (  /^ ) = div
unfold let (  %^ ) = rem
unfold let (  ^^ ) = logxor
unfold let (  &^ ) = logand
unfold let (  |^ ) = logor
unfold let ( <<^ ) = shift_left
unfold let ( >>^ ) = shift_right
unfold let (  =^ ) = op_Equality #t
unfold let (  >^ ) = gt
unfold let ( >=^ ) = gte
unfold let (  <^ ) = lt
unfold let ( <=^ ) = lte

(* To input / output constants *)
assume val to_string: t -> Tot string
assume val of_string: string -> Tot t

#set-options "--lax"
//This private primitive is used internally by the
//compiler to translate bounded integer constants
//with a desugaring-time check of the size of the number,
//rather than an expensive verification check.
//Since it is marked private, client programs cannot call it directly
//Since it is marked unfold, it eagerly reduces,
//eliminating the verification overhead of the wrapper
private
unfold
let __int_to_t (a:int) : Tot t
    = int_to_t a
#reset-options
