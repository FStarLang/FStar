module FStar.Trees

module M = FStar.Math.Lib

#set-options "--fuel 1 --ifuel 1 --z3rlimit 20"

(*** Type definitions *)

(**** The tree structure *)

type tree (a: Type) =
  | Leaf : tree a
  | Node: data: a -> left: tree a -> right: tree a -> tree a

(**** Binary search trees *)

type node_data (a b: Type) = {
  key: a;
  payload: b;
}

let kv_tree (a: Type) (b: Type) = tree (node_data a b)

class ordered (a: Type) = {
  compare: a -> a -> int
}

let rec forall_keys (#a: Type) (t: tree a) (cond: a -> bool) : bool =
  match t with
  | Leaf -> true
  | Node data left right ->
    cond data && forall_keys left cond && forall_keys right cond

let key_left (#a: Type) {| d: ordered a |} (root key: a) =
  d.compare root key >= 0

let key_right (#a: Type) {| d: ordered a |} (root key: a) =
  d.compare root key < 0

let rec is_bst (#a: Type) {| d: ordered a |} (x: tree a) : bool =
  match x with
  | Leaf -> true
  | Node data left right ->
    is_bst left && is_bst right &&
    forall_keys left (key_left data) &&
    forall_keys right (key_right data)

let bst (a: Type) {| d: ordered a |} = x:tree a {is_bst x}

(*** Operations *)

(**** Lookup *)

let rec mem (#a: Type) (r: tree a) (x: a) : prop =
  match r with
  | Leaf -> False
  | Node data left right ->
    (data == x) \/ (mem right x) \/ mem left x

let rec bst_search (#a: Type) {| d: ordered a |} (x: bst a) (key: a) : option a =
  match x with
  | Leaf -> None
  | Node data left right ->
    let delta = d.compare data key in
    if delta < 0 then bst_search right key else
    if delta > 0 then bst_search left key else
    Some data

(**** Height *)

let rec height (#a: Type) (x: tree a) : nat =
  match x with
  | Leaf -> 0
  | Node data left right ->
    if height left > height right then (height left) + 1
    else (height right) + 1

(**** Append *)

let rec append_left (#a: Type) (x: tree a) (v: a) : tree a =
  match x with
  | Leaf -> Node v Leaf Leaf
  | Node x left right -> Node x (append_left left v) right

let rec append_right (#a: Type) (x: tree a) (v: a) : tree a =
  match x with
  | Leaf -> Node v Leaf Leaf
  | Node x left right -> Node x left (append_right right v)


(**** Insertion *)

(**** BST insertion *)

let rec insert_bst (#a: Type) {| d: ordered a |} (x: bst a) (key: a) : tree a =
  match x with
  | Leaf -> Node key Leaf Leaf
  | Node data left right ->
    let delta = d.compare data key in
    if delta >= 0 then begin
      let new_left = insert_bst left key in
      Node data new_left right
    end else begin
      let new_right = insert_bst right key in
      Node data left new_right
    end

let rec insert_bst_preserves_forall_keys
  (#a: Type)
  {| d: ordered a |}
  (x: bst a)
  (key: a)
  (cond: a -> bool)
    : Lemma
      (requires (forall_keys x cond /\ cond key))
      (ensures (forall_keys (insert_bst x key) cond))
  =
  match x with
  | Leaf -> ()
  | Node data left right ->
    let delta = d.compare data key in
    if delta >= 0 then
      insert_bst_preserves_forall_keys left key cond
    else
      insert_bst_preserves_forall_keys right key cond

let rec insert_bst_preserves_bst
  (#a: Type)
  {| d: ordered a |}
  (x: bst a)
  (key: a)
    : Lemma(is_bst (insert_bst x key))
  =
  match x with
  | Leaf -> ()
  | Node data left right ->
    let delta = d.compare data key in
    if delta >= 0 then begin
      insert_bst_preserves_forall_keys left key (key_left data);
      insert_bst_preserves_bst left key
    end else begin
      insert_bst_preserves_forall_keys right key (key_right data);
      insert_bst_preserves_bst right key
    end

(**** AVL insertion *)

let rec is_balanced (#a: Type) (x: tree a) : bool =
  match x with
  | Leaf -> true
  | Node data left right ->
    M.abs(height right - height left) <= 1 &&
    is_balanced(right) &&
    is_balanced(left)

let is_avl (#a: Type) {| d: ordered a |} (x: tree a) : prop =
  is_bst(x) /\ is_balanced(x)

let avl (a: Type) {| d: ordered a |} = x: tree a {is_avl x}

let rotate_left (#a: Type) (r: tree a) : option (tree a) =
  match r with
  | Node x t1 (Node z t2 t3) -> Some (Node z (Node x t1 t2) t3)
  | _ -> None
  
let rotate_right (#a: Type) (r: tree a) : option (tree a) =
  match r with
  | Node x (Node z t1 t2) t3 -> Some (Node z t1 (Node x t2 t3))
  | _ -> None

let rotate_right_left (#a: Type) (r: tree a) : option (tree a) =
  match r with
  | Node x t1 (Node z (Node y t2 t3) t4) -> Some (Node y (Node x t1 t2) (Node z t3 t4))
  | _ -> None

let rotate_left_right (#a: Type) (r: tree a) : option (tree a) =
  match r with
  | Node x (Node z t1 (Node y t2 t3)) t4 -> Some (Node y (Node z t1 t2) (Node x t3 t4))
  | _ -> None

let rebalance_avl (#a: Type) {| d: ordered a |} (x: tree a) : tree a =
    match x with
    | Leaf -> x
    | Node data left right ->

      if is_balanced(x) then (x)
      else (

        if (height left - height right) > 1 then (
        match left with
        | Node ldata lleft lright ->
            if d.compare data ldata > 0 then (
            let r = rotate_left_right(x) in
            match r with
            | Some y -> y
            | _ -> x
            ) else (
            let r = rotate_right(x) in
            match r with
            | Some y -> y
            | _ -> x
            )
        | _ -> x

        ) else (
        if (height left - height right) < -1 then (
            match right with
            | Node rdata rleft rright ->
            if d.compare data rdata > 0 then (
                let r = rotate_left(x) in
                match r with
                | Some y -> y
                | _ -> x
                ) else (
                let r = rotate_right_left(x) in
                match r with
                | Some y -> y
                | _ -> x
            )
            | _ -> x
        ) else (
            x
        )
      )
    )
    
let rec insert_avl (#a: Type) {| d: ordered a |} (x: avl a) (key: a) : tree a =
  match x with
  | Leaf -> Node key Leaf Leaf
  | Node data left right ->
    let delta = d.compare data key in
    if delta >= 0 then (
      let new_left = insert_avl left key in
      let tmp = Node data new_left right in
      rebalance_avl(tmp)
    ) else (
      let new_right = insert_avl right key in
      let tmp = Node data left new_right in
      rebalance_avl(tmp)
    )

let insert_avl_preserves_avl
  (#a: Type)
  {| d: ordered a |}
  (x: avl a)
  (key: a)
    : Lemma(is_avl (insert_avl x key))
  =
  admit()
