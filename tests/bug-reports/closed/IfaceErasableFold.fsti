module IfaceErasableFold
val step (a: int) (z0 z1 z2 z3: int) : int
val zeta (i: nat) : Pure int (requires i < 128) (ensures fun r -> r >= -1664 /\ r <= 1664)
val layer (zeta_i: nat) (re: Seq.seq int) : Pure (int & Seq.seq int) (requires True) (ensures fun _ -> True)
