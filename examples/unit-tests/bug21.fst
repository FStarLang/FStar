module Bug21 

val constfun : 'a -> 'b -> Tot 'a
let constfun x _ = x


val ftrue_int : int -> Tot bool
let ftrue_int = constfun true

val ftrue : 'b -> Tot bool
let ftrue = constfun true
