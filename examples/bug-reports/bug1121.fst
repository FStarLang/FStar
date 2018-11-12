module Bug1121

let foo() : Tot int =
  match (1,3,2) with
  | (x,y,z) -> x
