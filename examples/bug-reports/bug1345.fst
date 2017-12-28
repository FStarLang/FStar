module Bug1345
let pos = n:nat {n>0} 
type t0 = n: pos -> unit
type t1 = n: nat {n>0} -> unit
let g (x:t0): t1 = x
////////////////////////////////////////////////////////////////////////////////
type t (a:nat) = x:nat{x <= a}
let foo #a (x:t a{x < 20}) = ()
let bar (y:t 17{y < 10}) = foo y
