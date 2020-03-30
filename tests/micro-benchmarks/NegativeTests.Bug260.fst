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
module NegativeTests.Bug260
type pnat =
  | O : pnat
  | S : pnat -> pnat

type validity : n:pnat -> Type =
  | VSucc : n:pnat -> Tot (validity (S n))
val bad : t:pnat -> Tot (validity (S (S t)))

[@(expect_failure [19])]
let bad t = VSucc t


(* Hard to keep this one in the suite since the program fails to even --lax check *)
(* module EscapingVariable *)
(* assume type Good : int -> Type *)
(* assume val enc: plain:int -> c:unit{Good plain} *)
(* assume val repr : int -> int *)

(* let f (text:int) = enc (repr text) //should fail; plain escapes *)
