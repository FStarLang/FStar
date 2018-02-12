module B

abstract type t1 =
  | D: int -> t1

abstract let foo (x:t1) :t1 = D 2

let bar (x:int) :int = x + 1
