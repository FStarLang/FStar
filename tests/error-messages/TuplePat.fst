module TuplePat

open FStar.Mul

let mult x y =
  match x, y with
  | 0, 0 -> 0
  | x, y -> x*y


let mult2 x y =
  match x, y with
  | Some x, Some y -> x*y
  | None, _
  | _, None -> 0
  | _ -> 123
