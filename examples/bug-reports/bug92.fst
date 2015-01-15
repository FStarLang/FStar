module Bug92

type t (a:Type) = a -> a -> Tot a

type f_type (a:Type) = r:t a{ forall x y. r x y = r y x }

assume val f : a:Type -> Tot (f_type a)

val f2 : a:Type -> a -> Tot a
let f2 x = f x x
