module Bug203

val dfst : #a:Type -> #b:(a -> Type) -> DTuple2 a b -> Tot a
let dfst t = MkDTuple2._1 t

val dsnd : a:Type -> b:(a -> Type) -> t:DTuple2 a b -> Tot (b (dfst t))
let dsnd t = MkDTuple2._2 t
