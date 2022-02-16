module Sequence

assume val f : nat -> unit
assume val g : nat -> unit

let test (n:nat) = f n; g n

