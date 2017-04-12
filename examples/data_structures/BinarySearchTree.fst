module BinarySearchTree

type tree =
  | Leaf : tree
  | Node : int -> tree -> tree -> tree

val in_tree : int -> tree -> Tot bool
let rec in_tree x t =
  match t with
  | Leaf -> false
  | Node n t1 t2 -> x = n || in_tree x t1 || in_tree x t2

val all : p:(int -> Tot bool) -> t:tree ->
            Tot (r:bool{r <==> (forall x. in_tree x t ==> p x)})
let rec all p t =
  match t with
  | Leaf -> true
  | Node n t1 t2 -> p n && all p t1 && all p t2

val is_bst : tree -> Tot bool
let rec is_bst t =
  match t with
  | Leaf -> true
  | Node n t1 t2 -> all (fun n' -> n > n') t1 &&
                    all (fun n' -> n < n') t2 && is_bst t1 && is_bst t2

val search : x:int -> t:tree{is_bst t} ->
  Tot (r:bool{r <==> in_tree x t})
let rec search x t =
  match t with
  | Leaf -> false
  | Node n t1 t2 -> if x = n then      true
                    else if x < n then search x t1
                    else               search x t2

val insert : x:int -> t:tree{is_bst t} ->
  Tot (r:tree{is_bst r /\ (forall y. in_tree y r <==> (in_tree y t \/ x = y))})
let rec insert x t =
  match t with
  | Leaf -> Node x Leaf Leaf
  | Node n t1 t2 -> if x = n then      t
                    else if x < n then Node n (insert x t1) t2
                    else               Node n t1 (insert x t2)
