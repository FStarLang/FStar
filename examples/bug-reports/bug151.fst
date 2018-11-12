module Bug151

open FStar.Array
open FStar.Seq

assume new type p: int -> nat -> Type

type int_1 = x:int{ p x 1 }
type int_2 = x:int{ p x 2 }

type seq_int_1 = seq int_1
type seq_int_2 = seq int_2

assume val eval:
  a:seq int -> len:nat{ len <= length a } -> Tot int

assume val bla2:
  a:seq_int_1{ length a = 10 } ->
  b:seq_int_2{ (length b = length a) /\ (eval a (length a) = eval b (length b)) }
