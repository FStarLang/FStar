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
module Neg

open FStar.ST
open FStar.Tactics

assume val __phi: Type
assume val __psi: Type
assume val  __xi: Type

let phi = squash __phi
let psi = squash __psi
let  xi = squash __xi

assume val c1 : unit -> ST unit (requires (fun h0 -> phi)) (ensures (fun h0 () h1 -> psi))
assume val c2 : unit -> ST unit (requires (fun h0 -> psi)) (ensures (fun h0 () h1 ->  xi))

val c3 : unit -> ST unit (requires (fun h0 -> phi)) (ensures (fun h0 () h1 -> xi))
let c3 () = c1 (); c2 (); assert_by_tactic xi idtac

// with_tactic is in negative position, should be peeled off!
val c4 : unit -> ST unit (requires (fun h0 -> phi)) (ensures (fun h0 () h1 -> xi))
let c4 () = c3 ()
