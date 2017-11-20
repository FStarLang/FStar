module Bug1341
let t (a:Type) = a -> (f:(nat -> nat){forall x. f x > x})
let incr : t bool = fun b x -> x + 1
