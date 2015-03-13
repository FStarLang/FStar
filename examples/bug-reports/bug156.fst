module Bug156

type tree =
  | Leaf : tree

val in_tree : int -> tree -> Tot bool
let rec in_tree x t =
  match t with
  | Leaf n -> false (* Note: Leaf doesn't take arguments! *)
