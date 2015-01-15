module FibIsOk

val fibonacci : nat -> Tot nat
let rec fibonacci n =
  if n <= 1 then 1 else fibonacci (n - 1) + fibonacci (n - 2)

val fib : nat -> nat -> n:nat -> Tot nat (decreases n)
let rec fib a b n =
  match n with
  | 0 -> a
  | _ -> fib b (a+b) (n-1)

val fib_is_ok_aux : i:nat -> n:nat{i<=n} ->
      Tot (u:unit{fib (fibonacci i) (fibonacci (i+1)) (n-i) = fibonacci n})
      (decreases (n-i))
let rec fib_is_ok_aux i n =
  if i=n then ()
  else fib_is_ok_aux (i+1) n

val fib_is_ok : n:nat -> Lemma (fib 1 1 n = fibonacci n)
let fib_is_ok n = fib_is_ok_aux 0 n
