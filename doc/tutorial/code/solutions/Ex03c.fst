module Ex03c
//fibonacci-property

val fibonacci : nat -> Tot nat
let rec fibonacci n =
  if n <= 1 then 1 else fibonacci (n - 1) + fibonacci (n - 2)

val fibonacci_greater_than_arg : n:nat{n >= 2} -> Lemma (fibonacci n >= n)
// BEGIN: FibonacciGreaterThanArgProof
let rec fibonacci_greater_than_arg n =
  match n with
  | 2 -> ()
  | _ -> fibonacci_greater_than_arg (n-1)

(*     
 Z3 proves the base case.
  
 The proof uses the induction hypothesis:
   forall x, 2 <= x < n ==> fibonacci x >= x
   
 Our goal is to prove that:
  fibonacci n >= n or equivalently fibonacci (n-1) + fibonacci (n-2) > n
  
 We make use of induction hypothesis to prove that 
  fibonacci (n-1) >= n-1
  
 For fibonacci (n-1) we use the property 
   forall x, fibonacci x > 1 
   
 This can be seen by giving fibonacci the stronger type
   val fibonacci : nat -> Tot (r:nat{r>=1})
   
 From this Z3 can proves the post condition 
*)

// END: FibonacciGreaterThanArgProof
