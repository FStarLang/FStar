module BitVectorEx

(* Like in FStar.BitVector.fst *)
open FStar.Seq
type bitVector_t (n: nat) = vec: seq bool {length vec = n}
