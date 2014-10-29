
module Stlc
open Prims.PURE

val typing : int
let typing =
  match 41, 42, Some 43 with
  | 41, 42, Some 43 -> 0
  | _, _, _         -> 0
  end
