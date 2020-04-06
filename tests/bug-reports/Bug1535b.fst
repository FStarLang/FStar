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
module Bug1535b

[@(expect_failure [3])]
exception E1 of (exn -> int)

[@(expect_failure [3])]
exception E2 of (exn -> exn)

[@(expect_failure [3])]
exception E3 of ((exn -> int) -> int)

[@(expect_failure [3])]
exception E4 of exn * (exn -> int)

[@(expect_failure [3])]
exception E5 of exn * (exn -> exn)

(* Here's how to exploit it if it succeeded: *)

// let f (e:exn) : exn =
//   match e with
//   | E1 f -> f e
//   | e -> e
//
// let g : exn = E1 f
//
// let h = f (E1 f) (* would loop on execution *)

(* Good ones *)
exception G0 of int
exception G1 of exn
exception G2 of (int -> exn)
exception G3 of (int -> exn * exn)
exception G4 of (int -> exn) * exn
