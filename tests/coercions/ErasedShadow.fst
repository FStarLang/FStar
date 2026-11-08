module ErasedShadow
open FStar.Ghost

(* A user coercion from [erased nat] must not shadow the builtin [reveal] for
   other [erased] types with the same target. *)
[@@coercion]
let en2i (n:erased nat) : GTot int = reveal n - 1

let from_erased_int (x:erased int) : GTot int = x
let from_erased_nat (x:erased nat) : GTot int = x
let _ = assert (forall (x:erased nat). from_erased_nat x == reveal x - 1)
let _ = assert (forall (x:erased int). from_erased_int x == reveal x)
