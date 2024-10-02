module Emb

[@@plugin]
type t =
  | A of int
  | B of int & bool
  | C : int -> string -> t

[@@plugin]
let f (x:int) = x + 123

[@@plugin]
let flip (x:t) : t =
  match x with
  | A x -> C x ""
  | B (i, b) -> B (-i, not b)
  | C x _ -> A x

[@@plugin]
type record = {a:int; b:bool}

let fr (x : record) : record =
  if x.b then { x with a = -x.a }
  else { x with b = true }
