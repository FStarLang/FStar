(** Integer multiplication, no special symbol. See FStar.Mul *)
[@smt_theory_symbol]
assume
val op_Multiply           : int -> int -> Tot int

(** [pow2 x] is [2^x]: *)
let rec pow2 (x:nat) : Tot pos =
  match x with
  | 0  -> 1
  | _  -> 2 `op_Multiply` (pow2 (x-1))
