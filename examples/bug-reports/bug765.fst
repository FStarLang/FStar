module Bug765

(* works *)
assume val foo': #n:nat -> Type -> Tot Type

(* works *)
assume val foo'': (n:nat) -> Type -> Tot Type

(* fails *)
assume val foo: (#n:nat) -> Type -> Tot Type
