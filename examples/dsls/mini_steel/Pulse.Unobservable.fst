module Pulse.Unobservable
open FStar.Tactics

let sealed_ (a:Type u#a) : Type u#a = a

let is_sealed (#a:Type u#a) (x:sealed_ a) : prop = True

let unobservable_eq (#a:Type u#a) (x y:sealed a)
  : Lemma
    (ensures x == y)
  = admit()
  
let observe (#a:Type u#a) (x:sealed a)
  : Tac a
  = x

let (let?) x f = f x
let return x = x
 
