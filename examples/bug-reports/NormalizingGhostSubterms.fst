module NormalizingGhostSubterms

assume val ghost: int -> GTot int

let test (x:int) =
  let y = ghost x in
  match x with
  | 0 -> y
  | _ -> x
