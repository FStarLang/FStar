module Bug1319c

assume val f: #a:Type -> a -> a -> unit

[@(expect_failure [54])]
let g x l = f x (Some x)
