module BinarySearchTreeBasic

type tree =
  | Leaf : tree
  | Node : n:int -> tree -> tree -> tree

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

val lt : int -> int -> Tot bool
let lt n1 n2 = n1 < n2

val gt : int -> int -> Tot bool
let gt n1 n2 = n1 > n2

val is_bst : tree -> Tot bool
let rec is_bst t =
  match t with
  | Leaf -> true
  | Node n t1 t2 -> all (gt n) t1 && all (lt n) t2 && is_bst t1 && is_bst t2

(* Changing to the following equivalent variant of is_bst triggers
   errors all over the rest of this file (filed as #339)
val is_bst : tree -> Tot bool
let rec is_bst t =
  match t with
  | Leaf -> true
  | Node n t1 t2 -> all (fun n' -> n > n') t1 &&
                    all (fun n' -> n' < n) t2 && is_bst t1 && is_bst t2
*)

val search : x:int -> t:tree{is_bst t} -> Tot (r:bool{r <==> in_tree x t})
let rec search x t =
  match t with
  | Leaf -> false
  | Node n t1 t2 -> if x = n then      true
                    else if x < n then search x t1
                    else               search x t2

val insert : x:int -> t:tree{is_bst t} ->
             Tot (r:tree{is_bst r /\
                  (forall y. in_tree y r <==> (in_tree y t \/ x = y))})
let rec insert x t =
  match t with
  | Leaf -> Node x Leaf Leaf
  | Node n t1 t2 -> if x = n then      t
                    else if x < n then Node n (insert x t1) t2
                    else               Node n t1 (insert x t2)

(* This variant also works, previously filed as #155 *)
val insert' : x:int -> t:tree -> Pure tree
               (requires (is_bst t))
               (ensures (fun r -> is_bst r /\
                 (forall y. in_tree y r <==> (in_tree y t \/ x = y))))
let rec insert' x t =
  match t with
  | Leaf -> Node x Leaf Leaf
  | Node n t1 t2 -> if x = n then      t
                    else if x < n then
                      (let y = insert' x t1 in 
                       Node n (insert' x t1) t2)
                    else
                      Node n t1 (insert' x t2)

(* One more variant with weak spec + extrinsic insert_lemma *)
val insert'' : int -> tree -> Tot tree
let rec insert'' x t =
  match t with
  | Leaf -> Node x Leaf Leaf
  | Node n t1 t2 -> if x = n then      t
                    else if x < n then Node n (insert'' x t1) t2
                    else               Node n t1 (insert'' x t2)

val insert_lemma : x:int -> t:tree{is_bst t} -> Lemma
      (is_bst (insert'' x t) /\
      (forall y. in_tree y (insert'' x t) <==> in_tree y t \/ x = y))
let rec insert_lemma x t = match t with
  | Leaf -> ()
  | Node _ t1 t2 -> insert_lemma x t1; insert_lemma x t2

val ge : int -> int -> Tot bool
let ge n1 n2 = n1 >= n2

val find_max : t:tree{is_bst t /\ is_Node t} ->
      Tot (x:int{all (ge x) t /\ in_tree x t})
let rec find_max (Node n _ t2) = if is_Leaf t2 then n else find_max t2

val find_max' : t:tree{is_Node t}-> Tot int
let rec find_max' (Node n _ t2) = if is_Leaf t2 then n else find_max' t2

val find_max_lemma : t:tree{is_Node t /\ is_bst t} ->
      Lemma (in_tree (find_max' t) t /\ all (ge (find_max' t)) t)
let rec find_max_lemma (Node _ _ t2) = if is_Node t2 then find_max_lemma t2

val find_max_eq : t:tree{is_Node t /\ is_bst t} -> Lemma (find_max t = find_max' t)
let find_max_eq t = find_max_lemma t

val delete : x:int -> t:tree{is_bst t} ->
  Tot (r:tree{is_bst r /\ not (in_tree x r)  /\
              (forall y. x <> y ==> (in_tree y t = in_tree y r))}) (decreases t)
let rec delete x t = match t with
  | Leaf -> Leaf
  | Node n t1 t2 -> if n = x then
                      match t1, t2 with
                      | Leaf, Leaf -> Leaf
                      | _   , Leaf -> t1
                      | Leaf, _    -> t2
                      | _           -> let y = find_max t1 in
                                       Node y (delete y t1) t2
                    else if x < n then Node n (delete x t1) t2
                                  else Node n t1 (delete x t2)

val delete' : x : int -> t:tree -> Tot tree (decreases t)
let rec delete' x t = match t with
  | Leaf -> Leaf
  | Node n t1 t2 -> if n = x then match (t1, t2) with
                      | (Leaf, Leaf) -> Leaf
                      | (_, Leaf) -> t1
                      | (Leaf, _) -> t2
                      | _ ->
                          let y = find_max' t1 in
                            Node y (delete' y t1) t2
                    else if x < n then Node n (delete' x t1) t2
                         else Node n t1 (delete' x t2)

val delete_lemma : x:int -> t:tree{is_bst t} ->
      Lemma (is_bst (delete' x t) /\ not (in_tree x (delete' x t)) /\
        (forall y. x <> y ==> (in_tree y (delete' x t) = in_tree y t)))
      (decreases t)
let rec delete_lemma x t = match t with
  | Leaf -> ()
  | Node n t1 t2 ->
     if x <> n then (delete_lemma x t1; delete_lemma x t2)
     else if is_Node t1 then (find_max_lemma t1; delete_lemma (find_max' t1) t1)
