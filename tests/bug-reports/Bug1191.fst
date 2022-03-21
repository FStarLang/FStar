module Bug1191

let rec mk_nary_function (dom codom: Type) (n: nat) : Type =
  if n = 0 then codom
  else dom -> mk_nary_function dom codom (n - 1)

let test0 : mk_nary_function int int 1 = fun (x: int) -> x

let test1 : normalize (mk_nary_function int int 1) = fun (x: int) -> x

let t n = if n = 0 then int -> int else string -> string
let test2 : t 0 = fun (x: int) -> x

let test3 : normalize (t 0) = fun (x: int) -> x
