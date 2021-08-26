module Steel.C.Typenat

(** Suppose [array (n : nat) (t : Type)] represents the type of array values.
    Then, when extracting values of type [ref (array n t)], the length n is lost.
    To make sure this information sticks around, this module provides
    an encoding of natural numbers as types. *)

val z: Type0
val s: Type0 -> Type0

let rec nat_t_of_nat (n: nat): Type0 =
  match n with
  | 0 -> z
  | n -> s (nat_t_of_nat (n - 1))
