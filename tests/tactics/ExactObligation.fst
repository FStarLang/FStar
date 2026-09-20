module ExactObligation

open FStar.Tactics.V2

let f (x:int) : Pure int (requires x >= 0) (ensures fun y -> y == x) = x

(* Elaborating [f 1] inside a tactic strands the [squash (1 >= 0)] implicit that
   carries [f]'s precondition, and [__exact_now] hands it back as a goal.  That
   goal has to go *behind* the one being solved: [exact] finishes with [solve],
   which dismisses the head of the goal list, so an obligation added in front
   would be the one dismissed -- leaving the implicit unsolved and reported as
   Error 217. *)
let answer : int = _ by (exact (`(f 1)))
