module Bug681

// Works
val f1: x:'a -> #u:unit -> Tot unit
let f1 x #u = ()

// Works
val f2: #u:unit -> x:'a -> Tot unit
let f2 #u (x:'a) = ()

assume type t: unit -> Type

// Works although recursive call doesn't have implicit argument
val f3: #u:unit -> x:'a -> y:t u -> nat -> Tot unit
let rec f3 #u (x:'a) y n =
  match n with
  | 0 -> ()
  | _ -> f3 x y (n-1)

// Inconsistent implicit argument annotation on argument x#157
val f4: #u:unit -> x:'a -> Tot unit
let f4 #u x = ()

// Expected expression of type "Type"; got expression "u" of type "Prims.unit"
val f5: #u:unit -> x:'a -> y:t u -> nat -> Tot unit
let rec f5 #u (x:'a) y n =
  match n with
  | 0 -> ()
  | _ -> f5 #u x y (n-1)
