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
