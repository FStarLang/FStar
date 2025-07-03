module Bug3366

let t = Type0 -> Type0

let x = list

let generic_apply #a #b (f: (a -> b) * nat) (x: a) : b * nat =
  (f._1 x, f._2)

let f (x: t * nat) =
  (generic_apply x nat)._2

let _ = f (x, 42) // <- crash
