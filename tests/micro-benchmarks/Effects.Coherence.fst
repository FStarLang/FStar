(*
   Copyright 2008-2020 Microsoft Research

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

module Effects.Coherence

(*
 * Unit tests for effects orderings
 *
 * In the simplified effect system an effect is just a name, and a lift is
 * just a rename: the specification of a computation is independent of its
 * effect.  What is still checked is the shape of the lattice, which is what
 * this file tests.
 *)

assume effect M1
assume effect M2
assume effect M3

assume sub_effect Tot ~> M1

(*
 * We build:
 *
 *   M1 --> M3
 *   M2 --> M3
 *)

assume sub_effect M1 ~> M3
assume sub_effect M2 ~> M3

assume val f1 : unit -> M1 unit

(* M1 can be lifted to M3 *)
let f2 () : M3 unit = f1 ()

assume val f4 : unit -> M3 unit

(* And M1 and M3 compose, via M3 *)
let f6 () : M3 unit = f1 (); f4 ()

(* But not the other way around: there is no lift out of M3 *)
[@@expect_failure]
let f7 () : M1 unit = f4 (); f1 ()

//Testing for cycles and unique upper bounds

assume effect M4
assume effect M5
assume effect M6
assume effect M7

(*
 * Make M6 the least upper bound of M4 and M5
 *)

assume sub_effect M4 ~> M6
assume sub_effect M5 ~> M6

(*
 * Try making M7 another upper bound of M4 and M5; it will fail
 *)

assume sub_effect M4 ~> M7
[@@expect_failure]
assume sub_effect M5 ~> M7

assume sub_effect M6 ~> M7

(*
 * This would induce a cycle, M5 -> M6 -> M7 -> M5
 *)
[@@expect_failure]
assume sub_effect M7 ~> M5
