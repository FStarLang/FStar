module Bug139

assume type A : Type
assume type B : Type

assume val f : #a:A -> b:B -> Tot bool

val bug : a:A -> b:B{f #a b} -> Tot unit
let rec bug a b = ()
