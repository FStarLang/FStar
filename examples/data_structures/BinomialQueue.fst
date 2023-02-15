module BinomialQueue

module L = FStar.List.Tot
open FStar.List.Tot

type key_t = nat

type tree =
  | Leaf : tree
  | Internal : tree -> key_t -> tree -> tree

let rec pow2heap_pred (depth:nat) (upper_bound:key_t) (t:tree) : prop =
  match t with
  | Leaf -> depth == 0
  | Internal left k right ->
    0 < depth /\
    k <= upper_bound /\
    pow2heap_pred (depth - 1) k left /\
    pow2heap_pred (depth - 1) upper_bound right

let is_pow2heap (depth:pos) (t:tree) : prop =
  match t with
  | Internal left k Leaf -> pow2heap_pred (depth - 1) k left
  | _ -> False

let rec is_ith_tail (i:pos) (l:list tree)
  : Tot prop (decreases l) =
  match l with
  | [] -> True
  | hd::tl ->
    (Leaf? hd \/ is_pow2heap i hd) /\ is_ith_tail (i + 1) tl

let rec all_leaf (l:list tree{Cons? l}) : bool =
  match l with
  | [Leaf] -> true
  | Leaf::tl -> all_leaf tl
  | _ -> false

let rec mk_compact (l:list tree) : list tree =
  match l with
  | [] -> []
  | _ ->
    if all_leaf l then []
    else let hd::tl = l in
         hd::(mk_compact tl)

let mk_compact_length (l:list tree{Cons? l})
  : Lemma (requires not (all_leaf l))
          (ensures L.length (mk_compact l) > 0)
  = ()

let last_cons (#a:Type) (x:a) (l:list a)
  : Lemma
      (requires Cons? l)
      (ensures L.last (x::l) == L.last l)
      [SMTPat (L.last (x::l))]
  = admit ()
    
let is_compact (l:list tree) = l == [] \/ Internal? (L.last l)

let rec mk_compact_correctness (l:list tree)
  : Lemma (is_compact (mk_compact l))
          [SMTPat (is_compact (mk_compact l))] =

  match l with
  | [] -> ()
  | _ ->
    if all_leaf l then ()
    else mk_compact_correctness (L.tl l)

let rec mk_compact_preserves_ith_tail (i:pos) (l:list tree)
  : Lemma
      (requires is_ith_tail i l)
      (ensures is_ith_tail i (mk_compact l))
      (decreases l)
      [SMTPat (is_ith_tail i (mk_compact l))] =
  match l with
  | [] -> ()
  | _ ->
    if all_leaf l then ()
    else mk_compact_preserves_ith_tail (i + 1) (L.tl l)

let rec keys_of_tree (t:tree) : list key_t =
  match t with
  | Leaf -> []
  | Internal left k right ->
    L.append (keys_of_tree left)
             (L.append [k] (keys_of_tree right))

let rec keys (q:list tree) : list key_t =
  match q with
  | [] -> []
  | hd::tl -> L.append (keys_of_tree hd) (keys tl)

let rec all_leaf_keys (l:list tree{Cons? l})
  : Lemma
      (requires Cons? l /\ all_leaf l)
      (ensures keys l == []) =
  match l with
  | [Leaf] -> ()
  | Leaf::tl -> all_leaf_keys tl

let rec compact_preserves_keys (q:list tree)
  : Lemma (keys q == keys (mk_compact q))
          [SMTPat (keys (mk_compact q))] =

  match q with
  | [] -> ()
  | _ ->
    if all_leaf q
    then all_leaf_keys q
    else compact_preserves_keys (L.tl q)
    
let is_priq (l:list tree) = is_ith_tail 1 l /\ is_compact l

type priq = l:list tree{is_priq l}

let empty : priq = []

let smash (depth:nat) (t1:tree) (t2:tree)
  : Pure tree
         (requires
            0 < depth /\ is_pow2heap depth t1 /\ is_pow2heap depth t2)
         (ensures fun t -> is_pow2heap (depth + 1) t) =

  match t1, t2 with
  | Internal left1 k1 Leaf, Internal left2 k2 Leaf ->
    if k1 <= k2
    then Internal (Internal left1 k1 left2) k2 Leaf
    else Internal (Internal left2 k2 left1) k1 Leaf

let rec carry (depth:nat) (q:list tree) (t:tree)
  : Pure (list tree)
         (requires
            0 < depth /\ is_ith_tail depth q /\ is_pow2heap depth t)
         (ensures fun q -> is_ith_tail depth q)
         (decreases L.length q) =
  match q with
  | [] -> [t]
  | Leaf::tl -> t::tl
  | hd::tl ->
    let q = carry (depth + 1) tl (smash depth hd t) in
    Leaf::q

let rec join (depth:nat) (p q:list tree) (c:tree)
  : Pure (list tree)
         (requires
            0 < depth /\
            is_ith_tail depth p /\
            is_ith_tail depth q /\
            (Leaf? c \/ is_pow2heap depth c))
         (ensures fun q -> is_ith_tail depth q)
         (decreases L.length p) =

  match p, q, c with
  | [], _, Leaf -> q
  | _, [], Leaf -> p
  | [], _, _ -> carry depth q c
  | _, [], _ -> carry depth p c
  | Leaf::tl_p, Leaf::tl_q, _ ->
    c::(join (depth + 1) tl_p tl_q Leaf)
  | hd_p::tl_p, Leaf::tl_q, Leaf ->
    hd_p::(join (depth + 1) tl_p tl_q Leaf)
  | Leaf::tl_p, hd_q::tl_q, Leaf ->
    hd_q::(join (depth + 1) tl_p tl_q Leaf)
  | Leaf::tl_p, hd_q::tl_q, _ ->
    Leaf::(join (depth + 1) tl_p tl_q (smash depth hd_q c))
  | hd_p::tl_p, Leaf::tl_q, _ ->
    Leaf::(join (depth + 1) tl_p tl_q (smash depth hd_p c))
  | hd_p::tl_p, hd_q::tl_q, c ->
    c::(join (depth + 1) tl_p tl_q (smash depth hd_p hd_q))

let priq_append (q:priq) (t:tree)
  : Lemma (requires
             is_ith_tail 1 q /\ is_pow2heap (L.length q + 1) t)
          (ensures is_ith_tail 1 (L.append q [t]))
  = admit ()

let rec unzip (depth:nat) (upper_bound:key_t) (t:tree)
  : Pure priq
         (requires
            pow2heap_pred depth upper_bound t)
         (ensures fun q -> L.length q == depth) =

  match t with
  | Leaf -> []
  | Internal left k right ->
    let q = unzip (depth - 1) upper_bound right in
    priq_append q (Internal left k Leaf);
    L.append_length q [Internal left k Leaf];
    assume (is_priq (L.append q [Internal left k Leaf]));
    L.append q [Internal left k Leaf]

let heap_delete_max (depth:pos) (t:tree)
  : Pure priq
         (requires is_pow2heap depth t)
         (ensures fun q -> L.length q == depth - 1) =

  match t with
  | Internal left k Leaf -> unzip (depth - 1) k left

let rec find_max (max:option key_t) (q:list tree)
  : Tot (option key_t) (decreases q) =
  match q with
  | [] -> max
  | Leaf::q -> find_max max q
  | (Internal _ k _)::q ->
    match max with
    | None -> find_max (Some k) q
    | Some max -> find_max (if max < k then Some k else Some max) q

let rec delete_max_aux (m:key_t) (depth:pos) (q:list tree)
  : Pure (list tree & priq)
         (requires is_ith_tail depth q)
         (ensures fun (q, _) -> is_ith_tail depth q)
         (decreases q) =

  match q with
  | [] -> [], []  // shouldn't happen
  | Leaf::q ->
    let q, new_q = delete_max_aux m (depth + 1) q in
    Leaf::q, new_q
  | (Internal left x right)::q ->
    if x < m
    then let q, new_q = delete_max_aux m (depth + 1) q in
         (Internal left x right)::q, new_q
    else Leaf::q, heap_delete_max depth (Internal left x right)

let delete_max (q:priq) : option (key_t & priq) =
  match find_max None q with
  | None -> None
  | Some m ->
    let q, new_q = delete_max_aux m 1 q in
    let r = join 1 q new_q Leaf in
    mk_compact_correctness r;
    Some (m, mk_compact r)

let insert (x:key_t) (q:priq) : priq =
  let l = carry 1 q (Internal Leaf x Leaf) in
  mk_compact l

let count_elt (x:key_t) (hd:key_t) : nat =
  if x = hd then 1 else 0

let rec count (x:key_t) (l:list key_t) : nat =
  match l with
  | [] -> 0
  | hd::tl -> (count_elt x hd) + count x tl

let rec count_append (l1 l2:list key_t) (x:key_t)
  : Lemma (count x (L.append l1 l2) ==
           count x l1 + count x l2)
          [SMTPat (count x (L.append l1 l2))] =

  match l1 with
  | [] -> ()
  | hd::tl -> count_append tl l2 x

let permutation (l1 l2:list key_t) =
  forall (x:key_t). count x l1 == count x l2

let permutation_append (l1 l2 l3 l4:list key_t)
  : Lemma
      (requires permutation l1 l3 /\ permutation l2 l4)
      (ensures permutation (l1@l2) (l3@l4)) =
  ()

let represents_t (t:tree) (l:list key_t) : prop =
  permutation (keys_of_tree t) l

let represents (q:list tree) (l:list key_t) : prop =
  permutation (keys q) l

let permutation_represents (l1 l2:list key_t) (q:priq)
  : Lemma
      (requires
         permutation l1 l2 /\
         q `represents` l1)
      (ensures q `represents` l2)
  = ()

let represents_permutation (l1 l2:list key_t) (q:priq)
  : Lemma
      (requires
         q `represents` l1 /\
         q `represents` l2)
      (ensures permutation l1 l2)
  = ()

// let empty_relate (l:list key_t)
//   : Lemma (requires [] `represents` l)
//           (ensures l == [])
//           [SMTPat ([] `represents` l)] =
//   admit ()

// let leaf_relate (l:list key_t)
//   : Lemma (requires Leaf `represents_t` l)
//           (ensures l == [])
//           [SMTPat (Leaf `represents_t` l)] =
//   admit ()

let smash_represents (depth:nat) (t1 t2:tree) (l1 l2:list key_t)
  : Lemma
      (requires
         0 < depth /\
         is_pow2heap depth t1 /\
         is_pow2heap depth t2 /\
         t1 `represents_t` l1 /\
         t2 `represents_t` l2)
      (ensures smash depth t1 t2 `represents_t` (L.append l1 l2)) =
  match t1, t2 with
  | Internal left1 k1 Leaf, Internal left2 k2 Leaf ->
    if k1 <= k2
    then begin
      L.append_assoc (keys_of_tree left1) [k1] (keys_of_tree left2);
      L.append_assoc (keys_of_tree t1) (keys_of_tree left2) [k2]
    end
    else begin
      L.append_assoc (keys_of_tree left2) [k2] (keys_of_tree left1);
      L.append_assoc (keys_of_tree t2) (keys_of_tree left1) [k1]
    end

let rec carry_represents (depth:nat) (q:list tree) (t:tree) (lq lt:list key_t)
  : Lemma
      (requires
         0 < depth /\
         is_ith_tail depth q /\
         is_pow2heap depth t /\
         q `represents` lq /\
         t `represents_t` lt)
      (ensures carry depth q t `represents` L.append lq lt)
      (decreases q) =

  match q with
  | [] -> ()
  | Leaf::_ -> ()
  | hd::tl ->
    smash_represents depth hd t (keys_of_tree hd) (keys_of_tree t);
    carry_represents (depth + 1) tl (smash depth hd t)
      (keys tl)
      (L.append (keys_of_tree hd) (keys_of_tree t));

    L.append_assoc (keys tl) (keys_of_tree hd) (keys_of_tree t)

let permutation_cons_snoc (x:key_t) (l:list key_t)
  : Lemma (permutation (x::l) (l @ [x])) = admit ()

let insert_represents (x:key_t) (q:priq) (l:list key_t)
  : Lemma
      (requires q `represents` l)
      (ensures insert x q `represents` (x::l)) =

  carry_represents 1 q (Internal Leaf x Leaf) l [x];
  permutation_cons_snoc x l

#push-options "--z3rlimit 100 --fuel 1 --ifuel 1"
let rec join_represents (depth:nat) (p q:list tree) (c:tree)
  (lp lq lc:list key_t)
  : Lemma
      (requires
         0 < depth /\
         is_ith_tail depth p /\
         is_ith_tail depth q /\
         (Leaf? c \/ is_pow2heap depth c) /\
         p `represents` lp /\
         q `represents` lq /\
         c `represents_t` lc)
      (ensures join depth p q c `represents` L.append lp (L.append lq lc))
      (decreases p) =

  let r = join depth p q c in
  match p, q, c with
  | [], _, Leaf
  | _, [], Leaf -> ()
  | [], _, _ -> carry_represents depth q c lq lc
  | _, [], _ -> carry_represents depth p c lp lc

  | Leaf::tl_p, Leaf::tl_q, _ ->
    join_represents (depth + 1) tl_p tl_q Leaf
      (keys tl_p) (keys tl_q) [];
    L.append_l_nil (keys tl_q);
    assert (permutation
              (keys_of_tree c @
               (keys tl_p @ keys tl_q))
              ((keys tl_p @ keys tl_q) @
               keys_of_tree c));
    L.append_assoc (keys tl_p)
                   (keys tl_q)
                   (keys_of_tree c)

  | hd_p::tl_p, Leaf::tl_q, Leaf ->
    join_represents (depth + 1) tl_p tl_q Leaf
      (keys tl_p) (keys tl_q) [];

    L.append_assoc (keys_of_tree hd_p) (keys tl_p) 
                   (keys tl_q @ []);
    
    permutation_append (keys q)
                       []
                       lq
                       lc;
    permutation_append (keys p)
                       ((keys q) @ [])
                       lp
                       (lq @ lc)
  | Leaf::tl_p, hd_q::tl_q, Leaf ->
    join_represents (depth + 1) tl_p tl_q Leaf
      (keys tl_p) (keys tl_q) [];
    L.append_l_nil (keys tl_q);

    assert (r `represents`
            (keys_of_tree hd_q @
             (keys tl_p @ keys tl_q)));

    assume (permutation
              (keys_of_tree hd_q @
               (keys tl_p @ keys tl_q))
              (keys tl_p @ (keys_of_tree hd_q @ keys tl_q)));

    permutation_append (keys q)
                       []
                       lq
                       lc;
    permutation_append (keys p)
                       ((keys q) @ [])
                       lp
                       (lq @ lc)
  | Leaf::tl_p, hd_q::tl_q, _ ->
    smash_represents depth hd_q c (keys_of_tree hd_q) (keys_of_tree c);
    join_represents (depth + 1) tl_p tl_q (smash depth hd_q c)
      (keys tl_p) (keys tl_q)
      (L.append (keys_of_tree hd_q) (keys_of_tree c));

    assert (r `represents`
            (keys tl_p @
             (keys tl_q @ (keys_of_tree hd_q @ keys_of_tree c))));

    assume (permutation
              (keys tl_p @
               (keys tl_q @ (keys_of_tree hd_q @ keys_of_tree c)))
              (keys tl_p @ ((keys_of_tree hd_q @ keys tl_q) @ keys_of_tree c)));

    permutation_append (keys q)
                       (keys_of_tree c)
                       lq
                       lc;
    permutation_append (keys p)
                       ((keys q) @ keys_of_tree c)
                       lp
                       (lq @ lc)

  | hd_p::tl_p, Leaf::tl_q, _ ->
    smash_represents depth hd_p c (keys_of_tree hd_p) (keys_of_tree c);
    join_represents (depth + 1) tl_p tl_q (smash depth hd_p c)
      (keys tl_p) (keys tl_q)
      (L.append (keys_of_tree hd_p) (keys_of_tree c));

    assert (r `represents`
            (keys tl_p @
             (keys tl_q @ (keys_of_tree hd_p @ keys_of_tree c))));

    assume (permutation
              (keys tl_p @
               (keys tl_q @ (keys_of_tree hd_p @ keys_of_tree c)))
              ((keys_of_tree hd_p @ keys tl_p) @
               (keys tl_q @ keys_of_tree c)));

    permutation_append (keys q)
                       (keys_of_tree c)
                       lq
                       lc;
    permutation_append (keys p)
                       ((keys q) @ keys_of_tree c)
                       lp
                       (lq @ lc)

  | hd_p::tl_p, hd_q::tl_q, c ->
    smash_represents depth hd_p hd_q (keys_of_tree hd_p) (keys_of_tree hd_q);
    join_represents (depth + 1) tl_p tl_q (smash depth hd_p hd_q)
      (keys tl_p) (keys tl_q)
      (L.append (keys_of_tree hd_p) (keys_of_tree hd_q));
    
    assert (r `represents`
            (keys_of_tree c @
             (keys tl_p @
              (keys tl_q @ (keys_of_tree hd_p @ keys_of_tree hd_q)))));

    assume (permutation
              (keys_of_tree c @
               (keys tl_p @
                (keys tl_q @ (keys_of_tree hd_p @ keys_of_tree hd_q))))
              ((keys_of_tree hd_p @ keys tl_p) @
               ((keys_of_tree hd_q @ keys tl_q) @
                (keys_of_tree c))));
    admit ();
    permutation_append (keys q)
                       (keys_of_tree c)
                       lq
                       lc;
    permutation_append (keys p)
                       ((keys q) @ keys_of_tree c)
                       lp
                       (lq @ lc)

let merge (p q:priq) : priq =
  let l = join 1 p q Leaf in
  mk_compact l

let merge_representation (p q:priq) (lp lq:list key_t)
  : Lemma
      (requires p `represents` lp /\ q `represents` lq)
      (ensures merge p q `represents` (lp @ lq)) =

  join_represents 1 p q Leaf lp lq []
