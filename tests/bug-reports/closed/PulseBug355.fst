module PulseBug355
open FStar.Ghost

assume val ref (t: Type0) : Type0
assume val pts_to #t (x: ref t) (v: t) : prop
assume val read #t (#x: ref t) (#v: erased t) (h: pts_to x v) : w:t { w == reveal v }

let foo (x: ref int) (v: erased nat) (h: pts_to x v) =
  read h
