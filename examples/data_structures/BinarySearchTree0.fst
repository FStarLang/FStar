module BinarySearchTree0

type tree =
  | Leaf : tree
  | Node : int -> tree -> tree -> tree

val search : int -> tree -> bool
let rec search x t =
  match t with
  | Leaf -> false
  | Node n t1 t2 -> if x = n then      true
                    else if x < n then search x t1
                    else               search x t2

val insert : int -> tree -> tree
let rec insert x t =
  match t with
  | Leaf -> Node x Leaf Leaf
  | Node n t1 t2 -> if x = n then      t
                    else if x < n then Node n (insert x t1) t2
                    else               Node n t1 (insert x t2)
