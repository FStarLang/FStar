module Eval

open Prims

// Basic arithmetic
#eval 1
#eval 1+1
#eval 3+4

// Function application / delta reduction
let double (x: int) = x + x
#eval double 5

// Higher-order functions
let apply_twice (f: int -> int) (x: int) = f (f x)
#eval apply_twice (fun x -> x + 1) 0

// Booleans
#eval not true
#eval (true && false)
#eval (true || false)

// Decidable equality
#eval (1 = 2)
#eval (1 = 1)

// If-then-else
#eval (if true then 1 else 2)
#eval (if false then 1 else 2)

// Lambda (stays as-is when not fully applied)
#eval (fun (x:int) -> x + 1)

// String
#eval "hello"
