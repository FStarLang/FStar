module Bug1605

type t =
  | C: f:int -> t

let foo (x:t) = C? x

let test () =
  let x = C 2 in
  assert (C? x)
