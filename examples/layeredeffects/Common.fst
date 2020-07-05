module Common

(* Common lemmas and constructions for layered effects examples. *)

let elim_pure #a #wp ($f : unit -> PURE a wp) p
 : Pure a (requires (wp p)) (ensures (fun r -> p r))
 //: PURE a (fun p' -> wp p /\ (forall r. p r ==> p' r))
 // ^ basically this, requires monotonicity
 = FStar.Monotonic.Pure.wp_monotonic_pure ();
   f ()
