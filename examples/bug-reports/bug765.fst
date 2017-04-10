module Bug765

(* works *)
val foo': #n:nat -> Type -> Tot Type

(* works *)
val foo'': (n:nat) -> Type -> Tot Type

(* fails *)
val foo: (#n:nat) -> Type -> Tot Type
