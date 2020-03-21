module Bug1952b

type q = #a:Type -> a -> a

let f : #b:Type -> q = fun #b #a x -> x

let g : #b:Type -> #a:Type -> a -> a = f
