module Steel.C.Typenat

val z: Type0
val s: Type0 -> Type0

let rec nat_t_of_nat (n: nat): Type0 =
  match n with
  | 0 -> z
  | n -> s (nat_t_of_nat (n - 1))
