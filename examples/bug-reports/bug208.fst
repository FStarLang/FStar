module Bug208

assume type acc (r:(int -> Type)) : Type

assume val acc_inv : #r:(int -> Type) -> acc r ->
              Tot (y:int -> Tot (r y))

assume val axiom1 : #b:Type -> f:(int -> Tot b) -> Lemma True

val fix_F : r:(int -> Type) -> acc r -> Tot unit
let rec fix_F (r:int->Type) a = axiom1 (acc_inv a)
