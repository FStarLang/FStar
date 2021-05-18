module Ch2
open FStar.Mul
let sqr_is_nat (x:int) : unit = assert (x * x >= 0)

[@@expect_failure[19]]
let sqr_is_pos (x:int) : unit = assert (x * x > 0)


//SNIPPET_START: max
let max x y = if x > y then x else y
let _ = assert (max 0 1 = 1)
let _ = assert (forall x y. max x y >= x /\
                            max x y >= y /\
                            (max x y = x \/ max x y = y))
//SNIPPET_END: max

let rec factorial (x:nat) : nat = if x = 0 then 1 else x * factorial (x - 1)

//SNIPPET_START: factorial_is_positive
let rec factorial_is_positive (x:nat)
  : u:unit{factorial x > 0}
  = if x = 0 then ()
    else factorial_is_positive (x - 1)
//SNIPPET_END: factorial_is_positive


//SNIPPET_START: factorial_is_pos
let rec factorial_is_pos (x:int)
  : Lemma (requires x >= 0)
          (ensures factorial x > 0)
  = if x = 0 then ()
    else factorial_is_pos (x - 1)
//SNIPPET_END: factorial_is_pos


//SNIPPET_START: factorial_is_greater_than_arg
let rec factorial_is_greater_than_arg (x:int)
  : Lemma (requires x > 2)
          (ensures factorial x > x)
  = if x = 3 then ()
    else factorial_is_greater_than_arg (x - 1)
//SNIPPET_END: factorial_is_greater_than_arg

//SNIPPET_START: fibonacci_question
let rec fibonacci (n:nat)
  : nat
  = if n <= 1
    then 1
    else fibonacci (n - 1) + fibonacci (n - 2)

val fibonacci_greater_than_arg (n:nat{n >= 2})
  : Lemma (fibonacci n >= n)
//SNIPPET_END: fibonacci_question

//SNIPPET_START: fibonacci_answer
let rec fibonacci_greater_than_arg (n:nat{n >= 2})
  : Lemma (fibonacci n >= n)
  = if n <= 3 then ()
    else (
      fibonacci_greater_than_arg (n - 1);
      fibonacci_greater_than_arg (n - 2)
    )
//SNIPPET_END: fibonacci_answer


//SNIPPET_START: fibonacci_answer_alt
let rec fib_greater_than_arg (n:nat{n >= 2})
  : Lemma (fibonacci n >= n)
  = if n = 2 then ()
    else (
      fib_greater_than_arg (n - 1)
    )
//SNIPPET_END: fibonacci_answer_alt
