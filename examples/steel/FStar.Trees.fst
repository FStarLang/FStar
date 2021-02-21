module FStar.Trees

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

let rec forall_keys (#a #b: Type) (t: kv_tree a b) (cond: a -> bool) : bool =
  match t with
  | Leaf -> true
  | Node data left right ->
    cond data.key && forall_keys left cond && forall_keys right cond

let key_left (#a: Type) {| d: ordered a |} (root key: a) =
  d.compare root key >= 0

let key_right (#a: Type) {| d: ordered a |} (root key: a) =
  d.compare root key < 0

let rec is_bst (#a #b: Type) {| d: ordered a |} (x: kv_tree a b) : bool =
  match x with
  | Leaf -> true
  | Node data left right ->
    is_bst left && is_bst right &&
    forall_keys left (key_left data.key) &&
    forall_keys right (key_right data.key)

let bst (a b: Type) {| d: ordered a |} = x:kv_tree a b{is_bst x}

(*** Operations *)

(**** Lookup *)

let rec mem (#a: Type) (r: tree a) (x: a) : prop =
  match r with
  | Leaf -> False
  | Node data left right ->
    (data == x) \/ (mem right x) \/ mem left x

let rec bst_search (#a #b: Type) {| d: ordered a |} (x: bst a b) (key: a) : option b =
  match x with
  | Leaf -> None
  | Node data left right ->
    let delta = d.compare data.key key in
    if delta < 0 then bst_search right key else
    if delta > 0 then bst_search left key else
    Some data.payload

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

let rec insert_bst (#a #b: Type) {| d: ordered a |} (x: bst a b) (key: a) (payload: b) : kv_tree a b =
  match x with
  | Leaf -> Node ({key; payload}) Leaf Leaf
  | Node data left right ->
    let delta = d.compare data.key key in
    if delta >= 0 then begin
      let new_left = insert_bst left key payload in
      Node data new_left right
    end else begin
      let new_right = insert_bst right key payload in
      Node data left new_right
    end

let rec insert_bst_preserves_forall_keys
  (#a #b: Type)
  {| d: ordered a |}
  (x: bst a b)
  (key: a)
  (payload: b)
  (cond: a -> bool)
    : Lemma
      (requires (forall_keys x cond /\ cond key))
      (ensures (forall_keys (insert_bst x key payload) cond))
  =
  match x with
  | Leaf -> ()
  | Node data left right ->
    let delta = d.compare data.key key in
    if delta >= 0 then
      insert_bst_preserves_forall_keys left key payload cond
    else
      insert_bst_preserves_forall_keys right key payload cond

let rec insert_bst_preserves_bst
  (#a #b: Type)
  {| d: ordered a |}
  (x: bst a b)
  (key: a)
  (payload: b)
    : Lemma(is_bst (insert_bst x key payload))
  =
  match x with
  | Leaf -> ()
  | Node data left right ->
    let delta = d.compare data.key key in
    if delta >= 0 then begin
      insert_bst_preserves_forall_keys left key payload (key_left data.key);
      insert_bst_preserves_bst left key payload
    end else begin
      insert_bst_preserves_forall_keys right key payload (key_right data.key);
      insert_bst_preserves_bst right key payload
    end

(**** AVL Trees *)

let avl (a b: Type) {| d: ordered a |} = x: kv_tree a b {is_bst x}

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

let rebalance_avl (#a #b: Type) {| d: ordered a |} (x: kv_tree a b) : kv_tree a b =
    match x with
    | Leaf -> x
    | Node data left right ->
 
      if (height right - height left) > 1 then (
      match left with
      | Node ldata lleft lright ->
        if d.compare data.key ldata.key > 0 then (
          let r = rotate_right(x) in
          match r with
          | Some y -> y
          | _ -> x
        ) else (
          let r = rotate_left_right(x) in
          match r with
          | Some y -> y
          | _ -> x
        )
      | _ -> x

    ) else (
      if (height right - height left) < -1 then (
        match right with
        | Node rdata rleft rright ->
          if d.compare data.key rdata.key > 0 then (
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
    
let rec insert_avl (#a #b: Type) {| d: ordered a |} (x: avl a b) (key: a) (payload: b): kv_tree a b =
  match x with
  | Leaf -> Node ({key; payload}) Leaf Leaf
  | Node data left right ->
    let delta = d.compare data.key key in
    if delta >= 0 then (
      let new_left = insert_avl left key payload in
      let tmp = Node data new_left right in
      rebalance_avl(tmp)
    ) else (
      let new_right = insert_avl right key payload in
      let tmp = Node data left new_right in
      rebalance_avl(tmp)
    )

let rec is_balanced (#a: Type) (x: tree a) : prop =
  match x with
  | Leaf -> True
  | Node data left right ->
    (height left - height right) <= 1 /\
    (height right - height left) <= 1 /\
    is_balanced(right) /\
    is_balanced(left)

let is_avl (#a #b: Type) {| d: ordered a |} (x: kv_tree a b) : prop =
  is_bst(x) /\ is_balanced(x)
