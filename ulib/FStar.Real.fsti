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
module FStar.Real
(*
  This module provides a signature for real arithmetic.

  Real number constants can be specific in floating point format with
  an 'R' suffix, e.g., 1.0R

  All these operations are mapped to the correspondings primitives
  in Z3's theory of real arithmetic.
*)

val real : eqtype

val of_int : int -> Tot real

val ( +. ) : real -> real -> Tot real
val ( -. ) : real -> real -> Tot real
val ( *. ) : real -> real -> Tot real
val ( /. ) : real -> d:real{d <> 0.0R} -> Tot real

val ( >.  ) : real -> real -> Tot bool
val ( >=. ) : real -> real -> Tot bool

val ( <.  ) : real -> real -> Tot bool
val ( <=. ) : real -> real -> Tot bool

#reset-options "--smtencoding.elim_box true --smtencoding.l_arith_repr native --smtencoding.nl_arith_repr native"
//Tests
let one : real = of_int 1
let two : real = of_int 2

val sqrt_2 : r:real{r *. r = two}

let n_over_n2 (n:real{n <> 0.0R /\ n*.n <> 0.0R}) = assert (n /. (n *. n) == 1.0R /. n)

let test = assert (two >. one)
let test1 = assert (one = 1.0R)

let test_lt1 = assert (1.0R <. 2.0R)
let test_lt2 = assert (~ (1.0R <. 1.0R))
let test_lt3 = assert (~ (2.0R <. 1.0R))

let test_le1 = assert (1.0R <=. 2.0R)
let test_le2 = assert (1.0R <=. 1.0R)
let test_le3 = assert (~ (2.0R <=. 1.0R))

let test_gt1 = assert (~ (1.0R >. 2.0R))
let test_gt2 = assert (~ (1.0R >. 1.0R))
let test_gt3 = assert (2.0R >. 1.0R)

let test_ge1 = assert (~ (1.0R >=. 2.0R))
let test_ge2 = assert (1.0R >=. 1.0R)
let test_ge3 = assert (2.0R >=. 1.0R)

let test_add_eq = assert (1.0R +. 1.0R = 2.0R)
let test_add_eq' = assert (1.0R +. 3.0R = 4.0R)
let test_add_lt = assert (1.0R +. 1.0R <. 3.0R)

let test_mul_eq = assert (2.0R *. 2.0R = 4.0R)
let test_mul_lt = assert (2.0R *. 2.0R <. 5.0R)

let test_div_eq = assert (8.0R /. 2.0R = 4.0R)
let test_div_lt = assert (8.0R /. 2.0R <. 5.0R)

let test_sqrt_2_mul = assert (sqrt_2 *. sqrt_2 = 2.0R)
//let test_sqrt_2_add = assert (sqrt_2 +. sqrt_2 >. 2.0R) // Fails
let test_sqrt_2_scale = assert (1.0R /. sqrt_2 = sqrt_2 /. 2.0R)

// Common identities
let add_id_l = assert (forall n. 0.0R +. n = n)
let add_id_r = assert (forall n. n +. 0.0R = n)

let mul_nil_l = assert (forall n. 0.0R *. n = 0.0R)
let mul_nil_r = assert (forall n. n *. 0.0R = 0.0R)

let mul_id_l = assert (forall n. 1.0R *. n = n)
let mul_id_r = assert (forall n. n *. 1.0R = n)

let add_comm = assert (forall x y. x +. y = y +.x)
let add_assoc = assert (forall x y z. (x +. y) +.z = (x +. y) +. z)

let mul_comm = assert (forall x y. x *. y = y *.x)
let mul_assoc = assert (forall x y z. (x *. y) *.z = (x *. y) *. z)
let mul_dist = assert (forall x y z. x *. (y +. z) = (x *. y) +. (x *.z))
