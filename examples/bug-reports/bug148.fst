module Bug148

open FStar.All

noeq type foo (r:(unit -> Type)) : Type =
  | Foo : x:unit -> (r x -> Tot (foo r)) -> foo r

val bug : r:(unit -> Type) -> x:unit -> foo r -> r x -> ML (foo r)
let bug x = function | Foo _ h1 -> h1
