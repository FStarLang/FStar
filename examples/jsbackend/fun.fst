module JSUnit.Functions

let rec ackermann m n = 
    match m, n with
    | 0, n -> n + 1
    | m, 0 -> ackermann (m - 1) 1
    | m, n -> ackermann (m - 1) (ackermann m (n - 1))

let rec fib n = match n with
  | 0 | 1 -> 1
  | n -> (fib (n-1)) + (fib (n-2))

let rec even n =
 match n with 0 -> true | 1 -> false | x -> odd (n-1)

and odd n =
 match n with 0 -> false | 1 -> true | x -> even (n-1)

let nil =
 JS.utest "Ackertmann(3,5)" (ackermann 3 5) 253 ;
 JS.utest "Fib(20)" (fib 20) 10946 ;
 JS.utest "Even(200)" (even 200) true
