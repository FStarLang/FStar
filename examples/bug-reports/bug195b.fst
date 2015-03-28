module Bug192b

assume val subst : int -> Tot int
assume type typing : int -> Type
val substitution : e:int -> Tot (typing (subst e))
let substitution e = magic()
