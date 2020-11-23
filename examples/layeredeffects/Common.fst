module Common

open FStar.Universe

(* Common lemmas and constructions for layered effects examples. *)

let curry f a b = f (a, b)
let uncurry f (a, b) = f a b

let coerce #a #b (x:a{a == b}) : b = x

let unreachable (#a:Type u#aa) () : Pure a (requires False) (ensures (fun _ -> False)) =
  coerce #(raise_t string) #a (raise_val "whatever")

let elim_pure #a #wp ($f : unit -> PURE a wp) p
 : Pure a (requires (wp p)) (ensures (fun r -> p r))
 //: PURE a (fun p' -> wp p /\ (forall r. p r ==> p' r))
 // ^ basically this, requires monotonicity
 = FStar.Monotonic.Pure.wp_monotonic_pure ();
   f ()

let bind_pure #a #b #wp1 #wp2 (c : unit -> PURE a wp1) (f : (x:a) -> PURE b (wp2 x))
  : PURE b (fun p -> wp1 (fun x -> wp2 x p))
 = FStar.Monotonic.Pure.wp_monotonic_pure ();
   f (c ())

let return_pure #a (x:a)
  : PURE a (fun p -> p x)
  = x
