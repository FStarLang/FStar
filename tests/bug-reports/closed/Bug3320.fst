module Bug3320

type t =
  | A { x:int; y:int }
  | B { z:bool }

let is_A (x:t) : bool =
  match x with
  | A {} -> true
  | _ -> false
