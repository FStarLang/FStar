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
module FStar.Real.Old

(* This module is DEPRECATED. Use FStar.Real instead. *)

open FStar.Real
module R = FStar.Real

let real = R.real
let of_int = R.of_int

(**
  Used to extract real constants; this function is
  uninterpreted logically. i.e., 1.1R is extracted to
  [of_string "1.1"]
  *)
val of_string: string -> Tot real

unfold let ( +. ) : real -> real -> Tot real                = R.op_Plus_Dot
unfold let ( -. ) : real -> real -> Tot real                = R.op_Subtraction_Dot
unfold let ( *. ) : real -> real -> Tot real                = R.op_Star_Dot
unfold let ( /. ) : real -> d:real{d <> 0.0R} -> Tot real   = R.op_Slash_Dot

(* Assuming ghost decidable equality, but it is not eqtype. *)
val ( =.  ) (x y : real) : GTot (b:bool{b <==> x == y})
val ( >.  ) (x y : real) : GTot (b:bool{b <==> R.op_Greater_Dot x y})
val ( >=. ) (x y : real) : GTot (b:bool{b <==> R.op_Greater_Equals_Dot x y})
val ( <.  ) (x y : real) : GTot (b:bool{b <==> R.op_Less_Dot x y})
val ( <=. ) (x y : real) : GTot (b:bool{b <==> R.op_Less_Equals_Dot x y})

unfold let zero   = R.zero
unfold let one    = R.one
unfold let two    = R.two
unfold let sqrt_2 = R.sqrt_2
