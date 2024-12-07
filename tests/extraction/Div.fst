module Div
open FStar.Mul

let collatz_body (f: (int -> Dv int)) (i: int) : Dv int =
  if i = 1
  then i
  else if i % 2 = 0
  then f (i / 2)
  else f (3 * i + 1)

let rec collatz (i: int) : Dv int = collatz_body collatz i

let rec f () : Dv int = f ()

let _ =
  let x = collatz 6171 in
  let y = if x = 1 then x else f () in
  1
