module MinusVsNegParsing

let test (x:int) : bool =
  match x with
  | (-5) -> true
  | -3 -> true
  | _ -> false

// Parses as a match against (-5)
val x : (y:int{y == -5}) -> int
let x - 5 = 1

// Parses as a match against (-5)
val y : (y:int{y == -5}) -> int
let y -5 = 1

(* Make sure we fail for negative *unsigned* machine ints. *)
[@@expect_failure] let _ = -1uy
[@@expect_failure] let _ = -1us
[@@expect_failure] let _ = -1ul
[@@expect_failure] let _ = -1uL
[@@expect_failure] let _ = -1sz
[@@expect_failure] let _ = -1z

let _ = 1uy
let _ = 1us
let _ = 1ul
let _ = 1uL
let _ = 1sz
let _ = 1z

(* All good for signed variants. *)

let _ = -1y
let _ = -1s
let _ = -1l
let _ = -1L

let _ = 1y
let _ = 1s
let _ = 1l
let _ = 1L
