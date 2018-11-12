module Bug1345b

type t (a:nat) = x:nat{x <= a}
let foo #a (x:t a{x < 20}) = ()
let bar (y:t 17{y < 10}) = foo y
