module Unit1.UnificationTests
assume type t : int -> Type
assume val f: int -> Tot int
assume val g: #x:int -> t (f x) -> Tot unit
let h1 (x: t (f 0)) = g x
let h2 (x: t ((fun x -> f (x - 1)) 1)) = g x

