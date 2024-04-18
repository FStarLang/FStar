(*
   Copyright 2008-2018 Microsoft Research

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
module Ex03b
//fibonacci


(* val fibonacci : int -> int *)
(* val fibonacci : int -> ML int (same as above) *)
(* val fibonacci : int -> Tot nat *)
(* val fibonacci : int -> Tot (y:int{y>=1}) *)
(* val fibonacci : x:int -> Tot (y:int{y>=1 /\ y >= x}) *)
(* val fibonacci : x:int -> Tot *)
(*   (y:int{y >= 1 /\ y >= x /\ (x>=3 ==> y>=2)}) *)
val fibonacci : int -> Tot (x:nat{x>0})
let rec fibonacci n =
  if n <= 1 then 1 else fibonacci (n - 1) + fibonacci (n - 2)
