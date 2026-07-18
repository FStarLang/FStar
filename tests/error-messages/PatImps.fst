module PatImps

let f1 (x:list 'a) : int =
  match x with
  | Nil -> 0
  | Cons _ _ -> 1

noeq
type t2 = | A : #x:int -> t2

let f2 (x:t2) : int =
  match x with
  | A #i -> i

noeq
type t3 =
  | B : #x:int -> t3
  | C : #x:int -> t3

let f3 (x:t3) : int =
  match x with
  | B #i -> i
  | C #i -> i
