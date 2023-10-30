module Harness
open FStar.Mul
open FStar.Classical

// Something that Z3 can't prove on its own
let bar (x z : nat) = exists (y:nat) (w:nat). z*y = x*w

private let aux (x z : nat) : Lemma (bar x z) =
  introduce exists y w. z*y = x*w with x z and ()

let foo (x : nat) : prop = forall z. bar x z
let always_foo x : Lemma (foo x) =
  introduce forall z. bar x z with aux x z
