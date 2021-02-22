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
  compare: a -> a -> int;
  refl: squash (forall x. compare x x == 0);
  antisym: squash (forall x y. compare x y > 0 <==> compare y x < 0);
  trans: squash (forall x y z. compare x y >= 0 /\ compare y z >= 0 ==> compare x z >= 0)
}

let rec forall_keys (#a: Type) (t: tree a) (cond: a -> bool) : bool =
  match t with
  | Leaf -> true
  | Node data left right ->
    cond data && forall_keys left cond && forall_keys right cond

let key_left (#a: Type) {| d: ordered a |} (root key: a) =
  d.compare root key >= 0

let key_right (#a: Type) {| d: ordered a |} (root key: a) =
  d.compare root key <= 0

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

(** rotate preserves bst *)
let rec forall_keys_trans (#a: Type) (t: tree a) (cond1 cond2: a -> bool)
  : Lemma (requires (forall x. cond1 x ==> cond2 x) /\ forall_keys t cond1)
          (ensures forall_keys t cond2)
  = match t with
  | Leaf -> ()
  | Node data left right ->
    forall_keys_trans left cond1 cond2; forall_keys_trans right cond1 cond2

let rotate_left_bst (#a:Type) {| d : ordered a |} (r:tree a)
  : Lemma (requires is_bst r /\ Some? (rotate_left r)) (ensures is_bst (Some?.v (rotate_left r)))
  = match r with
  | Node x t1 (Node z t2 t3) ->
      assert (is_bst (Node z t2 t3));
      assert (is_bst (Node x t1 t2));
      forall_keys_trans t1 (key_left x) (key_left z)

let rotate_right_bst (#a:Type) {| d : ordered a |} (r:tree a)
  : Lemma (requires is_bst r /\ Some? (rotate_right r)) (ensures is_bst (Some?.v (rotate_right r)))
  = match r with
  | Node x (Node z t1 t2) t3 ->
      assert (is_bst (Node z t1 t2));
      assert (is_bst (Node x t2 t3));
      forall_keys_trans t3 (key_right x) (key_right z)

let rotate_right_left_bst (#a:Type) {| d : ordered a |} (r:tree a)
  : Lemma (requires is_bst r /\ Some? (rotate_right_left r)) (ensures is_bst (Some?.v (rotate_right_left r)))
  = match r with
  | Node x t1 (Node z (Node y t2 t3) t4) ->
    assert (is_bst (Node z (Node y t2 t3) t4));
    assert (is_bst (Node y t2 t3));
    let left = Node x t1 t2 in
    let right = Node z t3 t4 in

    assert (forall_keys (Node y t2 t3) (key_right x));
    assert (forall_keys t2 (key_right x));
    assert (is_bst left);

    assert (is_bst right);

    forall_keys_trans t1 (key_left x) (key_left y);
    assert (forall_keys left (key_left y));

    forall_keys_trans t4 (key_right z) (key_right y);
    assert (forall_keys right (key_right y))


let rotate_left_right_bst (#a:Type) {| d : ordered a |} (r:tree a)
  : Lemma (requires is_bst r /\ Some? (rotate_left_right r)) (ensures is_bst (Some?.v (rotate_left_right r)))
  = match r with
  | Node x (Node z t1 (Node y t2 t3)) t4 ->
    // Node y (Node z t1 t2) (Node x t3 t4)
    assert (is_bst (Node z t1 (Node y t2 t3)));
    assert (is_bst (Node y t2 t3));
    let left = Node z t1 t2 in
    let right = Node x t3 t4 in

    assert (is_bst left);

    assert (forall_keys (Node y t2 t3) (key_left x));
    assert (forall_keys t2 (key_left x));
    assert (is_bst right);

    forall_keys_trans t1 (key_left z) (key_left y);
    assert (forall_keys left (key_left y));

    forall_keys_trans t4 (key_right x) (key_right y);
    assert (forall_keys right (key_right y))

(** Same elements before and after rotate **)

let rotate_left_key_left (#a:Type) {| d : ordered a |} (r:tree a) (root:a)
  : Lemma (requires forall_keys r (key_left root) /\ Some? (rotate_left r))
          (ensures  forall_keys (Some?.v (rotate_left r)) (key_left root))
  = match r with
  | Node x t1 (Node z t2 t3) ->
      assert (forall_keys (Node z t2 t3) (key_left root));
      assert (forall_keys (Node x t1 t2) (key_left root))

let rotate_left_key_right (#a:Type) {| d : ordered a |} (r:tree a) (root:a)
  : Lemma (requires forall_keys r (key_right root) /\ Some? (rotate_left r))
          (ensures  forall_keys (Some?.v (rotate_left r)) (key_right root))
  = match r with
  | Node x t1 (Node z t2 t3) ->
      assert (forall_keys (Node z t2 t3) (key_right root));
      assert (forall_keys (Node x t1 t2) (key_right root))

let rotate_right_key_left (#a:Type) {| d : ordered a |} (r:tree a) (root:a)
  : Lemma (requires forall_keys r (key_left root) /\ Some? (rotate_right r))
          (ensures  forall_keys (Some?.v (rotate_right r)) (key_left root))
  = match r with
  | Node x (Node z t1 t2) t3 ->
      assert (forall_keys (Node z t1 t2) (key_left root));
      assert (forall_keys (Node x t2 t3) (key_left root))

let rotate_right_key_right (#a:Type) {| d : ordered a |} (r:tree a) (root:a)
  : Lemma (requires forall_keys r (key_right root) /\ Some? (rotate_right r))
          (ensures  forall_keys (Some?.v (rotate_right r)) (key_right root))
  = match r with
  | Node x (Node z t1 t2) t3 ->
      assert (forall_keys (Node z t1 t2) (key_right root));
      assert (forall_keys (Node x t2 t3) (key_right root))

let rotate_right_left_key_left (#a:Type) {| d : ordered a |} (r:tree a) (root:a)
  : Lemma (requires forall_keys r (key_left root) /\ Some? (rotate_right_left r))
          (ensures  forall_keys (Some?.v (rotate_right_left r)) (key_left root))
  = match r with
  | Node x t1 (Node z (Node y t2 t3) t4) ->
    assert (forall_keys (Node z (Node y t2 t3) t4) (key_left root));
    assert (forall_keys (Node y t2 t3) (key_left root));
    let left = Node x t1 t2 in
    let right = Node z t3 t4 in
    assert (forall_keys left (key_left root));
    assert (forall_keys right (key_left root))


let rotate_right_left_key_right (#a:Type) {| d : ordered a |} (r:tree a) (root:a)
  : Lemma (requires forall_keys r (key_right root) /\ Some? (rotate_right_left r))
          (ensures  forall_keys (Some?.v (rotate_right_left r)) (key_right root))
  = match r with
  | Node x t1 (Node z (Node y t2 t3) t4) ->
    assert (forall_keys (Node z (Node y t2 t3) t4) (key_right root));
    assert (forall_keys (Node y t2 t3) (key_right root));
    let left = Node x t1 t2 in
    let right = Node z t3 t4 in
    assert (forall_keys left (key_right root));
    assert (forall_keys right (key_right root))

let rotate_left_right_key_left (#a:Type) {| d : ordered a |} (r:tree a) (root:a)
  : Lemma (requires forall_keys r (key_left root) /\ Some? (rotate_left_right r))
          (ensures  forall_keys (Some?.v (rotate_left_right r)) (key_left root))
  = match r with
  | Node x (Node z t1 (Node y t2 t3)) t4 ->
    // Node y (Node z t1 t2) (Node x t3 t4)
    assert (forall_keys (Node z t1 (Node y t2 t3)) (key_left root));
    assert (forall_keys (Node y t2 t3) (key_left root));
    let left = Node z t1 t2 in
    let right = Node x t3 t4 in

    assert (forall_keys left (key_left root));
    assert (forall_keys right (key_left root))

let rotate_left_right_key_right (#a:Type) {| d : ordered a |} (r:tree a) (root:a)
  : Lemma (requires forall_keys r (key_right root) /\ Some? (rotate_left_right r))
          (ensures  forall_keys (Some?.v (rotate_left_right r)) (key_right root))
  = match r with
  | Node x (Node z t1 (Node y t2 t3)) t4 ->
    // Node y (Node z t1 t2) (Node x t3 t4)
    assert (forall_keys (Node z t1 (Node y t2 t3)) (key_right root));
    assert (forall_keys (Node y t2 t3) (key_right root));
    let left = Node z t1 t2 in
    let right = Node x t3 t4 in

    assert (forall_keys left (key_right root));
    assert (forall_keys right (key_right root))


(** Balancing operation for AVLs *)

let rebalance_avl (#a: Type) {| d: ordered a |} (x: tree a) : tree a =
    match x with
    | Leaf -> x
    | Node data left right ->

      if is_balanced x then x
      else (

        if height left - height right > 1 then (
          let Node ldata lleft lright = left in
          if height lright > height lleft then (
            match rotate_left_right x with
            | Some y -> y
            | _ -> x
          ) else (
            match rotate_right x with
            | Some y -> y
            | _ -> x
          )

        ) else if height left - height right < -1 then (
          let Node rdata rleft rright = right in
            if height rleft > height rright then (
              match rotate_right_left x with
              | Some y -> y
              | _ -> x
            ) else (
              match rotate_left x with
              | Some y -> y
              | _ -> x
            )
        ) else (
          x
        )
      )


let rebalance_avl_proof (#a: Type) {| d: ordered a |} (x: tree a)
  (root:a)
  : Lemma
  (requires is_bst x /\ (
    match x with
    | Leaf -> True
    | Node data left right ->
      is_balanced left /\ is_balanced right /\
      height left - height right <= 2 /\
      height right - height left <= 2
    )
  )
  (ensures is_avl (rebalance_avl x) /\
     (forall_keys x (key_left root) ==> forall_keys (rebalance_avl x) (key_left root)) /\
     (forall_keys x (key_right root) ==> forall_keys (rebalance_avl x) (key_right root))
  )
  =
    match x with
    | Leaf -> ()
    | Node data left right ->
      let x_f = rebalance_avl x in
      let Node f_data f_left f_right = x_f in
      if is_balanced x then ()
      else (
        if height left - height right > 1 then (
          assert (height left = height right + 2);
          let Node ldata lleft lright = left in
          if height lright > height lleft then (
            assert (height left = height lright + 1);
            rotate_left_right_bst x;
            Classical.move_requires (rotate_left_right_key_left x) root;
            Classical.move_requires (rotate_left_right_key_right x) root;

            let Node y t2 t3 = lright in
            let Node x (Node z t1 (Node y t2 t3)) t4 = x in
            assert (f_data == y);
            assert (f_left == Node z t1 t2);
            assert (f_right == Node x t3 t4);
            assert (lright == Node y t2 t3);

            // Left part

            assert (is_balanced lright);
            assert (height t1 - height t2 <= 1);

            assert (height t2 - height t1 <= 1);

            assert (is_balanced t1);

            assert (is_balanced (Node y t2 t3));
            assert (is_balanced t2);

            assert (is_balanced f_left);


            // Right part
            assert (height t3 - height t4 <= 1);
            assert (height t4 - height t3 <= 1);

            assert (is_balanced t3);
            assert (is_balanced t4);
            assert (is_balanced f_right)

          ) else (
            rotate_right_bst x;
            Classical.move_requires (rotate_right_key_left x) root;
            Classical.move_requires (rotate_right_key_right x) root;

            assert (is_balanced f_left);
            assert (is_balanced f_right);
            assert (is_balanced x_f)
          )

        ) else if height left - height right < -1 then (
          let Node rdata rleft rright = right in
          if height rleft > height rright then (
            rotate_right_left_bst x;
            Classical.move_requires (rotate_right_left_key_left x) root;
            Classical.move_requires (rotate_right_left_key_right x) root;

            let Node x t1 (Node z (Node y t2 t3) t4) = x in
            assert (f_data == y);
            assert (f_left == Node x t1 t2);
            assert (f_right == Node z t3 t4);

            // Right part
            assert (is_balanced rleft);
            assert (height t3 - height t4 <= 1);
            assert (height t4 - height t4 <= 1);

            assert (is_balanced (Node y t2 t3));
            assert (is_balanced f_right);

            // Left part
            assert (is_balanced t1);
            assert (is_balanced t2);
            assert (is_balanced f_left)

          ) else (
            rotate_left_bst x;
            Classical.move_requires (rotate_left_key_left x) root;
            Classical.move_requires (rotate_left_key_right x) root;

            assert (is_balanced f_left);
            assert (is_balanced f_right);
            assert (is_balanced x_f)
          )
        )
      )

(** Insertion **)

let rec insert_avl (#a: Type) {| d: ordered a |} (x: avl a) (key: a) : tree a =
  match x with
  | Leaf -> Node key Leaf Leaf
  | Node data left right ->
    let delta = d.compare data key in
    if delta >= 0 then (
      let new_left = insert_avl left key in
      let tmp = Node data new_left right in
      rebalance_avl tmp
    ) else (
      let new_right = insert_avl right key in
      let tmp = Node data left new_right in
      rebalance_avl tmp
    )

#push-options "--z3rlimit 50"

let rec insert_avl_proof_aux (#a: Type) {| d: ordered a |} (x: avl a) (key: a)
  (root:a)

  : Lemma (requires is_avl x)
    (ensures (
      let res = insert_avl x key in
      is_avl res /\
      height x <= height res /\
      height res <= height x + 1 /\
      (forall_keys x (key_left root) /\ key_left root key ==> forall_keys res (key_left root)) /\
      (forall_keys x (key_right root) /\ key_right root key ==> forall_keys res (key_right root)))

    )
  = match x with
  | Leaf -> ()
  | Node data left right ->
    let delta = d.compare data key in
    if delta >= 0 then (
      let new_left = insert_avl left key in
      let tmp = Node data new_left right in

      insert_avl_proof_aux left key data;
      // Need this one for propagating that all elements are smaller than root
      insert_avl_proof_aux left key root;

      rebalance_avl_proof tmp root

    ) else (
      let new_right = insert_avl right key in
      let tmp = Node data left new_right in

      insert_avl_proof_aux right key data;
      insert_avl_proof_aux right key root;

      rebalance_avl_proof tmp root
    )

#pop-options

let insert_avl_proof (#a: Type) {| d: ordered a |} (x: avl a) (key: a)
  : Lemma (requires is_avl x) (ensures is_avl (insert_avl x key))
  = Classical.forall_intro (Classical.move_requires (insert_avl_proof_aux x key))
