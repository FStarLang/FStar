module CoallesceConstraints

open FStar.Class.Printable

(* tcresolve runs only once here. We should really check for it... *)
let test (x:int) =
  to_string x ^ to_string x ^ to_string x ^ to_string x ^
  to_string x ^ to_string x ^ to_string x ^ to_string x ^
  to_string x ^ to_string x ^ to_string x ^ to_string x ^
  to_string x ^ to_string x ^ to_string x ^ to_string x ^
  to_string x ^ to_string x ^ to_string x ^ to_string x ^
  to_string x ^ to_string x ^ to_string x ^ to_string x ^
  to_string x ^ to_string x ^ to_string x ^ to_string x ^
  to_string x ^ to_string x ^ to_string x ^ to_string x ^
  to_string x ^ to_string x ^ to_string x ^ to_string x ^
  to_string x ^ to_string x ^ to_string x ^ to_string x
