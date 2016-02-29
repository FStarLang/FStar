module Test
assume type seq : Type -> Type
assume val length : #a:Type -> seq a -> Tot nat
assume val create : #a:Type -> n:nat -> x:a -> Tot (seq a)
assume Create_len: forall (a:Type) (n:nat) (x:a). length (create n x) = n
type byte = uint8
type bytes = seq byte
type lbytes (l:nat) = b:bytes{length b = l}

module Test2
open Test
val empty_bytes : lbytes 0
let empty_bytes = create 0 0uy
