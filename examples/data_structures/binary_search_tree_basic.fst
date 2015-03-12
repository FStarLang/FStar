module BinarySearchTreeBasic

type tree =
  | Leaf : n:int -> tree
  | Node : n:int -> tree -> tree -> tree

val in_tree : int -> tree -> Tot bool
let rec in_tree x t =
  match t with
  | Leaf n -> x = n
  | Node n t1 t2 -> x = n || in_tree x t1 || in_tree x t2

val all : (int -> Tot bool) -> tree -> Tot bool
let rec all p t =
  match t with
  | Leaf n -> p n
  | Node n t1 t2 -> p n && all p t1 && all p t2

(* CH: don't these already have some non-operator form? *)
val lt : int -> int -> Tot bool
let lt n1 n2 = n1 < n2

val gt : int -> int -> Tot bool
let gt n1 n2 = n1 > n2

val is_bst : tree -> Tot bool
let rec is_bst t =
  match t with
  | Leaf n -> true
  | Node n t1 t2 -> all (gt n) t1 && all (lt n) t2 && is_bst t1 && is_bst t2

val aux : p:(int -> Tot bool) -> x:int -> t:tree -> Lemma
      (requires (not(p x) /\ all p t))
      (ensures (not (in_tree x t))) [SMTPat (all p t); SMTPat (in_tree x t)]
let rec aux p x t =
  match t with
  | Leaf x' -> ()
  | Node x' t1 t2 -> aux p x t1; aux p x t2

val search : x:int -> t:tree{is_bst t} -> Tot (r:bool{r <==> in_tree x t})
let rec search x t =
  match t with
  | Leaf n -> x = n
  | Node n t1 t2 -> if x = n then      true
                    else if x < n then search x t1
                    else               search x t2
