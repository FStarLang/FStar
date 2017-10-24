module Bug023

type ty = a:Type{hasEq a}
type env = int -> Tot (option ty)
val extend : env -> int -> ty -> Tot env
let extend g x t = fun x' -> if x = x' then Some t else g x'

val extend_eq : g:env -> x:int -> a:ty -> Lemma
      (ensures ((extend g x a) x) = Some a)
let extend_eq g x a = ()
