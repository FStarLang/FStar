module Pulse.Unobservable
open FStar.Tactics

let t_ (a:Type u#a) : Type u#a = a

let is_unobservable (#a:Type u#a) (x:t_ a) : prop = True

let unobservable_eq (#a:Type u#a) (x y:t a)
  : Lemma
    (ensures x == y)
  = admit()
  
let observe (#a:Type u#a) (x:t a)
  : Tac a
  = x

 
