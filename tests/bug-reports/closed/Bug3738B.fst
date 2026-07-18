module Bug3738B

let f x =
  match x with
  | Bug3738A.A -> 1
