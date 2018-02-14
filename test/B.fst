module B

abstract type t1 =
  | A: t1
  | B: t1

private let foo (x:t1{A? t1}) :int = 0
