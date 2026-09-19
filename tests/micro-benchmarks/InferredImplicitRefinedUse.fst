module InferredImplicitRefinedUse

open FStar.Real

(* A recursive function whose implicit argument has an *inferred* type.  The
   variable standing for that type is bounded above by [perm] -- a refinement
   -- from [use1], and by [x:?u (n-1) {decreases ...}] from the recursive
   call, a bound that mentions the variable itself.  Combining the two
   produces an equation that fails the occurs check; the meet/join must not
   attempt it, or it gives up and widens the type all the way to [real],
   losing the refinement [use1] asked for.

   This is [Pulse.Lib]'s [(#[full_default ()] f: _)] idiom, which is how it
   turns up in practice. *)

type perm : Type0 = r:real { r >. 0.0R }

assume val use1 (f:perm) : int

let rec h (n:nat) (#f:_) : int =
  match n with
  | 0 -> 0
  | _ -> use1 f + h (n-1) #f
