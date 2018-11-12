module Bug1480

let rec f (x:nat) : nat =
    if x > 0
    then f (x-1)
    else 42
and g y = ()
