module Bug815

val push : int -> list int -> Tot (s:(list int){Cons? s})
let push = Cons
