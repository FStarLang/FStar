
(*******************************************************************)
(*** A more complex CPS function: adding the elements of a tree. ***)
(*******************************************************************)
module Expr

type expr =
  | Const : int -> expr
  | Plus : expr -> expr -> expr
