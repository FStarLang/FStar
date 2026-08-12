module LemmaCall

/// `Lemma` is now nothing more than an abbreviation for
///   `Pure unit (requires pre) (ensures fun _ -> post)`.
/// Calling one must add `pre` to the VC and make `post` available afterwards.

assume val f : int -> Tot int

assume
val f_mono (x:int) (y:int)
  : Lemma (requires (x <= y)) (ensures (f x <= f y))

let use_lemma (x:int) : Pure unit (requires True) (ensures (fun _ -> True)) =
  f_mono x (x + 1);
  assert (f x <= f (x + 1))

/// A `Lemma` used inside a `Pure` function body.
let bounded (x:int) : Pure int (requires True) (ensures (fun r -> r >= f x)) =
  f_mono x (x + 1);
  f (x + 1)

/// Ghost computations may be used to justify Pure ones, but not the reverse.
assume val ghost_witness : x:int -> Ghost int (requires True) (ensures (fun r -> r == f x))

let ghost_use (x:int) : Ghost int (requires True) (ensures (fun r -> r == f x)) =
  ghost_witness x
