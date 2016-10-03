module SimpleTest

val fibonacci: nat -> Tot nat
let rec fibonacci = function
  | 0
  | 1 -> 1
  | n -> fibonacci (n - 1) + fibonacci (n - 2)

let x = fibonacci(10)
