module Bug128

val subst : x:int -> Tot unit (decreases (if x = 42 then LexTop else LexTop))
let rec subst x = ()
