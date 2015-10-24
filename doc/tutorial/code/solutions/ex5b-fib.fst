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

(* You can write nested recursive functions, as you'd expect *)
val fib_inner_aux : nat -> Tot nat
let fib_inner_aux n =
  let rec aux : a:nat -> b:nat -> n:nat -> Tot nat (decreases n) =
    fun a b n -> match n with
      | 0 -> a
      | _ -> aux b (a + b) (n - 1) in
  aux 1 1 n

(* But, proving that the nested aux correctly computes fibonacci is
   hard, because you can't get you can't get your hands on that
   nested recursive aux function.
   Here's one way to do it. *)
val fib_inner_aux_2 : n:nat -> Tot (f:nat{f=fibonacci n})
let fib_inner_aux_2 n =
  let rec aux : a:nat -> b:nat -> n:nat
             -> Pure nat (requires true)
                       (ensures (fun m -> forall (k:nat{n <= k}). {:pattern (fibonacci k)} a=fibonacci (k - n) /\ b=fibonacci (k - n + 1) ==> m=fibonacci k))
                       (decreases n) =
    fun a b n -> match n with
      | 0 -> a
      | _ -> aux b (a + b) (n - 1) in
  aux 1 1 n
