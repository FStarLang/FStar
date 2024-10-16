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
module FStar.Int8

(**** THIS MODULE IS GENERATED AUTOMATICALLY USING [mk_int.sh], DO NOT EDIT DIRECTLY ****)

open FStar.Int
open FStar.Mul

#set-options "--max_fuel 0 --max_ifuel 0"

(* NOTE: anything that you fix/update here should be reflected in [FStar.UIntN.fstp], which is mostly
 * a copy-paste of this module. *)

type t : eqtype =
  | Mk: v:int_t n -> t


let v x = x.v

irreducible
let int_to_t x = Mk x

let uv_inv _ = ()

let vu_inv _ = ()

let v_inj _ _ = ()

let zero = int_to_t 0

let one =
  FStar.Math.Lemmas.pow2_lt_compat (n - 1) 1;
  int_to_t 1

let add a b = Mk (add (v a) (v b))

let sub a b = Mk (sub (v a) (v b))

let mul a b = Mk (mul (v a) (v b))

let div a b = Mk (div (v a) (v b))

let rem a b = Mk (mod (v a) (v b))

let logand x y = Mk (logand (v x) (v y))

let logxor x y = Mk (logxor (v x) (v y))

let logor x y = Mk (logor (v x) (v y))

let lognot x = Mk (lognot (v x))

let shift_right a s = Mk (shift_right (v a) (UInt32.v s))

let shift_left a s = Mk (shift_left (v a) (UInt32.v s))

let shift_arithmetic_right a s = Mk (shift_arithmetic_right (v a) (UInt32.v s))

let to_string _ = admit ()

//AR: this is to workaround the interleaving semantics of pragmas in FStar.Int128.fst
//    where the interface requires the last but one definition to be lax-checked
#push-options "--admit_smt_queries true"

let of_string _ = admit ()

#pop-options
