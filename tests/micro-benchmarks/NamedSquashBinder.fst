module NamedSquashBinder

(* The desugaring of a [requires] clause lifts it out as an anonymous trailing
   implicit [squash] binder, and [split_squash_binders] takes it back off before
   a [Lemma]'s postcondition and SMT patterns are read.  A binder the *user*
   wrote and then mentions is not that binder: dropping it while its name was
   still live made the checker fail with "Bound term variable not found h". *)

let in_ensures (x:int) (#h:squash True) : Lemma (ensures h == ()) = ()

(* One that is mentioned nowhere is still dropped, pattern or no pattern --
   which is what keeps it from becoming a quantified variable that the pattern
   does not bind. *)
let unused_with_pat (x:int) (#h:squash (x >= 0)) :
  Lemma (ensures x + 0 == x) [SMTPat (x + 0)] = ()

(* And so is the anonymous one that a [requires] generates. *)
let generated (x:int) : Lemma (requires x >= 0) (ensures x - 0 == x) = ()
