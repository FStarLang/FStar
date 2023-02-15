module Pulse.Unobservable
open FStar.Tactics

val sealed_ ([@@@strictly_positive] a:Type u#a) : t:Type u#a { hasEq t }

val is_sealed (#[@@@strictly_positive] a:Type u#a) (x:sealed_ a) : prop

let sealed a = x:sealed_ a{is_sealed x}

val unobservable_eq (#a:Type u#a) (x y:sealed a)
  : Lemma
    (ensures x == y)
    [SMTPat (is_sealed x);
     SMTPat (is_sealed y)]

val observe (#a:Type u#a) (x:sealed a)
  : Tac a

val (let?) (x:sealed 'a) (f: ('a -> sealed 'b)) : sealed 'b
val return (x:'a) : sealed 'a
