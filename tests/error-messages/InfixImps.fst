module InfixImps

let ( ++ ) #t (xs ys : list t) = xs

let foo = [1] ++ [2]
