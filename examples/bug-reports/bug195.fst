module Bug195

assume type deduce : int -> Type
assume val p : int -> Tot int
val hoare_while : i:int -> Tot (deduce (p i))
let hoare_while i = magic()
