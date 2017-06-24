module ValueArray

module S = FStar.Seq
module B = FStar.BufferNG

type t (a : Type) (n : UInt32.t)

assume val v : #a:Type -> #n:UInt32.t -> t a n -> s:S.seq a{ S.length s = UInt32.v n }
assume val of_buffer : #a:Type -> n:UInt32.t -> b:B.buffer a{ B.length b = n } -> t a n
assume val get : #a:Type -> #n:UInt32.t -> t a n -> i:UInt32.t{ UInt32.v i < UInt32.v n } -> a
