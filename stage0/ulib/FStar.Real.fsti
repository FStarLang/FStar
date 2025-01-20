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

  All these operations are mapped to the corresponding primitives
  in Z3's theory of real arithmetic.

  This is only a logical model of the reals. There is no extraction
  for them, as they are an erasable type. Any operation that can observe
  a real (comparisons, etc) must be Ghost or a proposition.
*)

[@@erasable]
val real : Type0

val of_int : int -> Tot real

val ( +. ) : real -> real -> Tot real
val ( -. ) : real -> real -> Tot real
val ( *. ) : real -> real -> Tot real
val ( /. ) : real -> d:real{d =!= 0.0R} -> Tot real

val ( >.  ) : real -> real -> prop
val ( >=. ) : real -> real -> prop

val ( <.  ) : real -> real -> prop
val ( <=. ) : real -> real -> prop

let zero : real = of_int 0
let one  : real = of_int 1
let two  : real = of_int 2
val sqrt_2 : r:real{r >=. 0.0R /\ r *. r == two}
