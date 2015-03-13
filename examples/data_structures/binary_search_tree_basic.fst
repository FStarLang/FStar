module BinarySearchTreeBasic

type tree =
  | Leaf : tree
  | Node : n:int -> tree -> tree -> tree

val in_tree : int -> tree -> Tot bool
let rec in_tree x t =
  match t with
  | Leaf n -> false
  | Node n t1 t2 -> x = n || in_tree x t1 || in_tree x t2

val all : (int -> Tot bool) -> tree -> Tot bool
let rec all p t =
  match t with
  | Leaf n -> true
  | Node n t1 t2 -> p n && all p t1 && all p t2

val all_correct : p:(int -> Tot bool) -> t:tree -> Lemma (requires True)
      (ensures (all p t <==> (forall x. in_tree x t ==> p x))) [SMTPat (all p t)]
let rec all_correct p t =
  match t with
  | Leaf -> ()
  | Node x' t1 t2 -> all_correct p t1; all_correct p t2

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

val search : x:int -> t:tree{is_bst t} -> Tot (r:bool{r <==> in_tree x t})
let rec search x t =
  match t with
  | Leaf n -> false
  | Node n t1 t2 -> if x = n then      true
                    else if x < n then search x t1
                    else               search x t2

(* This variant should also work, filed as #155
val insert : x:int -> t:tree -> Pure tree
               (requires (is_bst t))
               (ensures (fun r -> is_bst r /\
                 (forall y. in_tree y r <==> (in_tree y t \/ x = y))))
let rec insert x t =
  match t with
  | Leaf -> Node x Leaf Leaf
  | Node n t1 t2 -> if x = n then      t
                    else if x < n then
                      (assert (is_bst (insert x t1)); (* WTF? *)
                       admit() (*Node n (insert x t1) t2*))
                    else
                      admit()(*Node n t1 (insert x t2)*)
*)

val insert : x:int -> t:tree{is_bst t} ->
             Tot (r:tree{is_bst r /\
                  (forall y. in_tree y r <==> (in_tree y t \/ x = y))})
let rec insert x t =
  match t with
  | Leaf -> Node x Leaf Leaf
  | Node n t1 t2 -> if x = n then      t
                    else if x < n then Node n (insert x t1) t2
                    else               Node n t1 (insert x t2)
