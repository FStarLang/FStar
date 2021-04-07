module Dec

val f (x y:nat) : unit

val f1 (x y:nat) : unit
val f2 (x y:nat) : unit

val pred (x y:nat) : prop

val g (x:nat) (y:nat)
  : Lemma (requires x <= y)
          (ensures pred x y)

val h (x:nat) (y:nat)
  : Lemma (requires x <= y)
          (ensures pred x y)
