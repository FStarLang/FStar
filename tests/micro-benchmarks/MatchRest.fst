module MatchRest

type t (z : int) : bool -> Type =
  | A : int -> int -> t z true
  | B : int -> t z false
  | C : #_:int -> int -> t z true
  | D : #_:int -> #_:int -> t z false

let tag (#b:bool) : t 123 b -> int =
  function
  | A .. -> 1
  | B .. -> 2
  | C .. -> 3
  | D .. -> 4

[@@expect_failure [203]]
let bad (#b:bool) : t 123 b -> int =
  function
  | .. -> 1

let deep (x : option (option int)) : int =
  match x with
  | Some (Some ..) -> 2
  | Some None -> 1
  | None -> 0
