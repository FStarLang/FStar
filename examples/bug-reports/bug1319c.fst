module Bug1319c

assume val f: #a:Type -> a -> a -> unit

[@(fail [54])]
let g x l = f x (Some x)
