module Bug206

open FStar.Constructive

assume val proof_irrelevance : #a:Type -> x:a -> y:a -> Tot (ceq x y)

val contradiction : cfalse
let contradiction = ceq_eq (proof_irrelevance true false)
