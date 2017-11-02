module Bug139

assume type t1 : Type
assume type t2 : Type

assume val f : #a:t1 -> b:t2 -> Tot bool

val bug : a:t1 -> b:t2{f #a b} -> Tot unit
let rec bug a b = ()
