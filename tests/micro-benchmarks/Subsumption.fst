module Subsumption

/// Computation subtyping is now a plain implication between pre/postconditions
/// plus an edge in the effect lattice:
///   M t pre1 post1 <: N t pre2 post2
/// iff  M <= N,  pre2 ==> pre1,  and  pre2 ==> forall x. post1 x ==> post2 x.

assume val f : x:int -> Pure int (requires (x >= 0)) (ensures (fun r -> r == x + 1))

/// Strengthening the precondition and weakening the postcondition is allowed.
let weaker (x:int) : Pure int (requires (x >= 10)) (ensures (fun r -> r > 0)) =
  f x

/// PURE is below GHOST, so a pure computation may be used where a ghost one is
/// expected.
let pure_to_ghost (x:nat) : Ghost int (requires True) (ensures (fun r -> r == x + 1)) =
  f x

/// ... but not the other way around.
assume val g : x:int -> Ghost int (requires True) (ensures (fun r -> r == x))

[@@ expect_failure]
let ghost_to_pure (x:int) : Pure int (requires True) (ensures (fun r -> r == x)) =
  g x

/// Effect abbreviations conjoin the pre/postcondition written at the use site
/// with the one in the abbreviation, so `Tot` is `PURE` with a trivial spec.
let tot_is_pure (x:nat) : Tot int = f x

/// A `Tot` computation is usable at any `Pure` type whose precondition holds.
let tot_to_pure (x:int) : Pure int (requires True) (ensures (fun r -> r == x)) =
  x
