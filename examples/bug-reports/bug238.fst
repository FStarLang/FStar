module Bug238

type box = | Box : False -> box

val silly : a:Type -> a -> False
[@expect_failure 114]
let silly (a:Type) x = let Box y = x in y
