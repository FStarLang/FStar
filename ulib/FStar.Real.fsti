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

//Tests
let one : real = of_int 1
let two : real = 2.0R

val sqrt_2 : r:real{r *. r = two}
let test = assert (two >. one)
