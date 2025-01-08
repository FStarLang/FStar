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
module FStar.UInt8

(**** THIS MODULE IS GENERATED AUTOMATICALLY USING [mk_int.sh], DO NOT EDIT DIRECTLY ****)

open FStar.UInt
open FStar.Mul

#set-options "--max_fuel 0 --max_ifuel 0"

type t : eqtype =
  | Mk: v:uint_t n -> t

let v x = x.v

irreducible
let uint_to_t x = Mk x

let uv_inv _ = ()

let vu_inv _ = ()

let v_inj _ _ = ()

let zero = uint_to_t 0

let one = uint_to_t 1

let add a b = Mk (add (v a) (v b))

let add_underspec a b = Mk (add_underspec (v a) (v b))

let add_mod a b = Mk (add_mod (v a) (v b))

let sub a b = Mk (sub (v a) (v b))

let sub_underspec a b = Mk (sub_underspec (v a) (v b))

let sub_mod a b = Mk (sub_mod (v a) (v b))

let mul a b = Mk (mul (v a) (v b))

let mul_underspec a b = Mk (mul_underspec (v a) (v b))

let mul_mod a b = Mk (mul_mod (v a) (v b))

let div a b = Mk (div (v a) (v b))

let rem a b = Mk (mod (v a) (v b))

let logand x y = Mk (logand (v x) (v y))

let logxor x y = Mk (logxor (v x) (v y))

let logor x y = Mk (logor (v x) (v y))

let lognot x = Mk (lognot (v x))

let shift_right a s = Mk (shift_right (v a) (UInt32.v s))

#push-options "--z3rlimit 80 --fuel 1"  //AR: working around the interleaving semantics of pragmas

let shift_left a s = Mk (shift_left (v a) (UInt32.v s))

let lemma_sub_msbs a b
    = from_vec_propriety (to_vec (v a)) 1;
      from_vec_propriety (to_vec (v b)) 1;
      from_vec_propriety (to_vec (v (sub_mod a b))) 1

#pop-options

let to_string _ = admit ()

let to_string_hex _ = admit ()

let to_string_hex_pad _ = admit ()

let of_string _ = admit ()
