module Part2.Option
let bind #a #b
         (f: option a)
         (g: a -> option b)
  : option b
  = admit()

let return #a (x:a)
  : option a
  = admit()

let eq #a (f g : option a) = f == g

let left_identity #a #b (x:a) (g: a -> option b)
  : Lemma ((v <-- return x; g v) `eq` g x)
  = admit()
let right_identity #a (f:option a)
  : Lemma ((x <-- f; return x) `eq` f)
  = admit()
let associativity #a #b #c (f1:option a) (f2:a -> option b) (f3:b -> option c)
  : Lemma ((x <-- f1; y <-- f2 x; f3 y) `eq`
           (y <-- (x <-- f1; f2 x); f3 y))
  = admit()
