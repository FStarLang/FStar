module BinaryTrees

type tree =
  | Leaf : tree
  | Node : root:int -> left:tree -> right:tree -> tree

val size : tree -> Tot nat
let rec size t =
  match t with
  | Leaf -> 0
  | Node n t1 t2 -> 1 + size t1 + size t2

val map : f:(int -> Tot int) -> tree -> Tot tree
let rec map f t =
  match t with
  | Leaf -> Leaf
  | Node n t1 t2 -> Node (f n) (map f t1) (map f t2)

val map_size : f:(int -> Tot int) -> t:tree -> Lemma (size (map f t) = size t)
let rec map_size f t =
  match t with
  | Leaf -> ()
  | Node n t1 t2 -> map_size f t1; map_size f t2

val find : p:(int -> Tot bool) -> tree -> Tot (option int)
let rec find p t =
  match t with
  | Leaf -> None
  | Node n t1 t2 -> if p n then Some n else
                    if Some? (find p t1) then find p t1
                                         else find p t2

val find_some : p:(int -> Tot bool) -> t:tree ->
  Lemma (None? (find p t) \/ p (Some?.v (find p t)))
let rec find_some p t =
  match t with
  | Leaf -> ()
  | Node n t1 t2 -> find_some p t1; find_some p t2

let map_option f o = match o with
                    | Some n -> Some (f n)
                    | None   -> None

let compose f1 f2 x = f1 (f2 x)

val map_find : p:(int -> Tot bool) -> f:(int -> Tot int) -> t:tree ->
  Lemma (find p (map f t) = map_option f (find (compose p f) t))
let rec map_find p f t =
  match t with
  | Leaf -> ()
  | Node n t1 t2 -> map_find p f t1; map_find p f t2

val in_tree : int -> tree -> Tot bool
let rec in_tree x t =
  match t with
  | Leaf -> false
  | Node n t1 t2 -> x = n || in_tree x t1 || in_tree x t2

val fold : (int -> 'a -> 'a -> 'a) -> 'a -> tree -> 'a
let rec fold f a t =
  match t with
  | Leaf -> a
  | Node n t1 t2 -> f n (fold f a t1) (fold f a t2)

val fold_map : fm:(int -> int) -> ff:(int -> int -> int -> int) -> a:int -> t:tree ->
  Lemma (fold ff a (map fm t) = fold (compose ff fm) a t)
let rec fold_map fm ff a t =
  match t with
  | Leaf -> ()
  | Node n t1 t2 -> fold_map fm ff a t1; fold_map fm ff a t2

val size_fold : t:tree ->
  Lemma (size t = fold #nat (fun _ s1 s2 -> 1 + s1 + s2) 0 t)
let rec size_fold t =
  match t with
  | Leaf -> ()
  | Node n t1 t2 -> size_fold t1; size_fold t2

val in_tree_fold : x:int -> t:tree ->
  Lemma (in_tree x t = fold (fun n b1 b2 -> x = n || b1 || b2) false t)
let rec in_tree_fold x t =
  match t with
  | Leaf -> ()
  | Node n t1 t2 -> in_tree_fold x t1; in_tree_fold x t2

val find_fold : f:(int -> Tot bool) -> tree -> Tot (option (x:int{f x}))
let find_fold f = fold #(option (x:int{f x}))
                        (fun n o1 o2 -> if f n then Some n else
                                        if Some? o1 then o1 else o2) None

val revert : tree -> Tot tree
let rec revert t =
  match t with
  | Leaf -> Leaf
  | Node n t1 t2 -> Node n (revert t2) (revert t1)

(* simpler than for lists because revert is symmetric, while List.rev is not *)
val revert_involutive : t:tree -> Lemma (revert (revert t) = t)
let rec revert_involutive t =
  match t with
  | Leaf -> ()
  | Node n t1 t2 -> revert_involutive t1; revert_involutive t2

(* again, much simpler than for lists *)
val revert_injective : t1:tree -> t2:tree ->
  Lemma (requires (revert t1 = revert t2)) (ensures (t1 = t2))
let rec revert_injective t1 t2 =
  match t1, t2 with
  | Leaf, Leaf -> ()
  | Node n t11 t12, Node n t21 t22 -> revert_injective t11 t21;
                                      revert_injective t12 t22

val revert_fold : t:tree ->
  Lemma (revert t = fold (fun n t1 t2 -> Node n t2 t1) Leaf t)
let rec revert_fold t =
  match t with
  | Leaf -> ()
  | Node n t1 t2 -> revert_fold t1; revert_fold t2

(* open FStar.List *)

(* val list_of : tree -> Tot (list int) *)
(* let list_of = fold (fun n t1 t2 -> t1 @ [n] @ t2) [] *)

val remove_root : t:tree{Node? t} -> Tot tree
let rec remove_root t =
  match t with
  | Node n t1 t2 -> if Leaf? t1 then t2
                    else Node (Node?.root t1) (remove_root t1) t2


val add_root : x:int -> t:tree -> Tot (t':tree{Node? t'}) (decreases t)
let rec add_root x t =
  match t with
  | Leaf -> Node x Leaf Leaf
  | Node n t1 t2 -> Node x (add_root n t1) t2

(* remove and add implemented this way round-trip; TODO: does the converse hold? *)
val remove_add_root : x:int -> t:tree ->
  Lemma (requires True) (ensures (remove_root (add_root x t) = t))
        (decreases t)
let rec remove_add_root x t =
  match t with
  | Leaf -> ()
  | Node n t1 t2 -> remove_add_root x t1

let rec count (x:int) (t:tree) : Tot nat =
  match t with
  | Leaf -> 0
  | Node n t1 t2 -> (if n = x then 1 else 0) + count x t1 + count x t2

let rec remove (x:int) (t:tree{count x t > 0}) : Tot tree (decreases t) =
  match t with
  | Node n t1 t2 -> if x = n then remove_root t else
                    if count x t1 > 0 then Node n (remove x t1) t2
                                      else Node n t1 (remove x t2)

//This proof is flaky with Z3-4.5.0,
//It seems to require too much fuel to go through, although it should only need 2
//Z3-4.5.1 nightly successfully solves it with initial_fuel 2
//NS: 05/08 added a pattern on y to stabilize the proof
#reset-options "--z3rlimit 20 --initial_fuel 2 --initial_ifuel 2"
let rec count_remove_root (t:tree{Node? t}) :
    Lemma (ensures (let r = Node?.root t in
                   (count r (remove_root t) = count r t - 1) /\
                   (forall y.{:pattern (count y (remove_root t))} y <> r ==> count y (remove_root t) = count y t))) =
  let Node n t1 t2 = t in
  if Leaf? t1 then () 
  else count_remove_root t1

#reset-options
let rec count_remove (x:int) (t:tree{count x t > 0}) :
    Lemma (requires True)
          (ensures (count x (remove x t) = count x t - 1)) (decreases t) =
  match t with
  | Node n t1 t2 -> if x = n then count_remove_root t else
                    if count x t1 > 0 then count_remove x t1
                                      else count_remove x t2

