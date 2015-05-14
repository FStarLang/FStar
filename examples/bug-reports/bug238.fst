module Bug238

type box = | Box : int -> box

val silly : a:Type -> a -> int
let silly (a:Type) x = let Box y = x in y+1
