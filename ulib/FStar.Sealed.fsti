module FStar.Sealed

(* _sealed and isSealed only exist so we can write a good pattern
for the lemma below. You should always use `sealed` outside of this
module. *)

assume new type _sealed
  ([@@@strictly_positive] a : Type u#aa) : Type0

irreducible
let isSealed
  (#[@@@strictly_positive] a:Type u#aa)
  (x : _sealed a)
  : Type0 = unit

let sealed ([@@@strictly_positive] a : Type u#aa) : Type0 =
  x:(_sealed a){isSealed x}

val sealed_singl (#a:Type) (x y : _sealed a)
  : Lemma (x == y) [SMTPat (isSealed x); SMTPat (isSealed y)]

val seal (#a : Type u#aa) (x:a) : sealed a
val (let?) (#a : Type u#aa) (#b : Type u#bb) (x : sealed a) (f : a -> sealed b) : sealed b

let return = seal
