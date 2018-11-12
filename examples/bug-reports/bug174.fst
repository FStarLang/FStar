module Bug174

val foo : #x:int -> #y:int -> Tot unit (decreases x)
let rec foo h = ()
