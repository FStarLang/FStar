module DisjunctivePatterns

let foo xs =
  match xs with
  | []
  | x::xs' -> x
