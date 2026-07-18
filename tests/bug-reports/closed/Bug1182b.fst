module Bug1182b

type unOp 'a = 'a -> 'a

val twice : unOp 'a -> unOp 'a
let rec twice f x = f (f x)
