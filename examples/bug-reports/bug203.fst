module Bug203

val dfst : #a:Type -> #b:(a -> Type) -> dtuple2 a b -> Tot a
let dfst t = Mkdtuple2?._1 t

val dsnd : #a:Type -> #b:(a -> Type) -> t:dtuple2 a b -> Tot (b (dfst t))
let dsnd t = Mkdtuple2?._2 t
