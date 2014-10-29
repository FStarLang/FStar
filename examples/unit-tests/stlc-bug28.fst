
module Stlc
open Prims.PURE

val typing : option int
let typing =
  match 41, 42, Some 43 with
  | 41, 42, Some 43 -> None
  | _, _, _         -> None
  end
