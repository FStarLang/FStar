module Bug208

assume type acc (a:Type) (r:(a -> a -> Type)) (x:a) : Type

assume val acc_inv : r:('a -> 'a -> Type) -> x:'a -> a:(acc 'a r x) ->
              Tot (y:'a -> r y x -> Tot (acc 'a r y))

assume val axiom1 : #a:Type -> #b:Type -> f:(a -> Tot b) -> Lemma True

val fix_F : r:(int -> int -> Type) ->
            x:int -> acc int r x -> Tot unit
let rec fix_F x a = axiom1 (acc_inv x a)
