module CPS.Expr

type expr =
  | Const : int -> expr
  | Plus : expr -> expr -> expr
