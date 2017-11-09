module Bug092

type t (a:Type{hasEq a}) = a -> a -> Tot a

type f_type (a:Type{hasEq a}) = r:t a{ forall x y. r x y = r y x }

assume val f : #a:Type{hasEq a} -> Tot (f_type a)

val f2 : a:Type{hasEq a} -> a -> Tot a
let f2 x = f x x
