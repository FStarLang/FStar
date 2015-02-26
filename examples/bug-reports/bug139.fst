module Bug139

assume type A : Type
assume type B : Type

assume type p : b:B -> Type
assume val f : #a:A -> b:B -> Tot B

val bug : b:B -> a:A{p (f #a b)} -> Tot unit
let rec bug b a = ()
