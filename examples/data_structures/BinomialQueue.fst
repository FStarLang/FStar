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

let rec last_cons (#a:Type) (x:a) (l:list a)
  : Lemma
      (requires Cons? l)
      (ensures L.last (x::l) == L.last l)
      [SMTPat (L.last (x::l))] =

  match l with
  | [_] -> ()
  | _::tl -> last_cons x tl
    
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

module S = FStar.Set

noeq
type ms = {
  ms_count : key_t -> nat;
  ms_elems : S.set key_t;
}

let ms_empty : ms = {
  ms_count = (fun _ -> 0);
  ms_elems = S.empty;
}

let ms_singleton (x:key_t) : ms = {
  ms_count = (fun x' -> if x' = x then 1 else 0);
  ms_elems = S.singleton x;
}

let ms_append (ms1 ms2:ms) : ms = {
  ms_count = (fun x -> ms1.ms_count x + ms2.ms_count x);
  ms_elems = S.union ms1.ms_elems ms2.ms_elems;
}

let permutation (ms1 ms2:ms) =
  S.equal ms1.ms_elems ms2.ms_elems /\
  (forall (x:key_t).{:pattern ms1.ms_count x \/ ms2.ms_count x} ms1.ms_count x == ms2.ms_count x)
              
let rec keys_of_tree (t:tree) : ms =
  match t with
  | Leaf -> ms_empty
  | Internal left k right ->
    ms_append (keys_of_tree left)
              (ms_append (ms_singleton k) (keys_of_tree right))

let rec keys (q:list tree) : ms =
  match q with
  | [] -> ms_empty
  | hd::tl -> ms_append (keys_of_tree hd) (keys tl)

let rec all_leaf_keys (l:list tree{Cons? l})
  : Lemma
      (requires Cons? l /\ all_leaf l)
      (ensures permutation (keys l) ms_empty) =
  match l with
  | [Leaf] -> ()
  | Leaf::tl -> all_leaf_keys tl

let rec compact_preserves_keys (q:list tree)
  : Lemma (permutation (keys q) (keys (mk_compact q)))
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
  : Pure (key_t & list tree & priq)
         (requires is_ith_tail depth q)
         (ensures fun (x, q, _) -> m <= x /\ is_ith_tail depth q)
         (decreases q) =

  match q with
  | [] -> m + 1, [], []  // shouldn't happen
  | Leaf::q ->
    let x, q, new_q = delete_max_aux m (depth + 1) q in
    x, Leaf::q, new_q
  | (Internal left x right)::q ->
    if x < m
    then let y, q, new_q = delete_max_aux m (depth + 1) q in
         y, (Internal left x right)::q, new_q
    else x, Leaf::q, heap_delete_max depth (Internal left x right)

let delete_max (q:priq) : option (key_t & priq) =
  match find_max None q with
  | None -> None
  | Some m ->
    let _, q, new_q = delete_max_aux m 1 q in
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

// let permutation (l1 l2:list key_t) =
//   forall (x:key_t). count x l1 == count x l2

// let permutation_append (l1 l2 l3 l4:list key_t)
//   : Lemma
//       (requires permutation l1 l3 /\ permutation l2 l4)
//       (ensures permutation (l1@l2) (l3@l4)) =
//   ()

let repr_t (t:tree) (l:ms) : Type0 =
  permutation (keys_of_tree t) l

let repr (q:list tree) (l:ms) : Type0 =
  permutation (keys q) l

let ms_append_assoc (ms1 ms2 ms3:ms)
  : Lemma (permutation (ms_append ms1 (ms_append ms2 ms3))
                       (ms_append (ms_append ms1 ms2) ms3))
  = ()

let ms_permutation_trans (ms1 ms2 ms3:ms)
  : Lemma (requires permutation ms1 ms2 /\ permutation ms2 ms3)
          (ensures permutation ms1 ms3)
  = ()

let ms_permutation_sym (ms1 ms2:ms)
  : Lemma (requires permutation ms1 ms2)
          (ensures permutation ms2 ms1)
  = ()

let smash_represents (depth:nat) (t1 t2:tree) (l1 l2:ms)
  : Lemma
      (requires
         0 < depth /\
         is_pow2heap depth t1 /\
         is_pow2heap depth t2 /\
         t1 `repr_t` l1 /\
         t2 `repr_t` l2)
      (ensures smash depth t1 t2 `repr_t` (ms_append l1 l2)) = ()

let rec carry_represents (depth:nat) (q:list tree) (t:tree) (lq lt:ms)
  : Lemma
      (requires
         0 < depth /\
         is_ith_tail depth q /\
         is_pow2heap depth t /\
         q `repr` lq /\
         t `repr_t` lt)
      (ensures carry depth q t `repr` ms_append lq lt)
      (decreases q) =

  match q with
  | [] -> ()
  | Leaf::_ -> ()
  | hd::tl ->
    smash_represents depth hd t (keys_of_tree hd) (keys_of_tree t);
    carry_represents (depth + 1) tl (smash depth hd t)
      (keys tl)
      (ms_append (keys_of_tree hd) (keys_of_tree t))

let insert_represents (x:key_t) (q:priq) (l:ms)
  : Lemma
      (requires q `repr` l)
      (ensures insert x q `repr` (ms_append (ms_singleton x) l)) =
  carry_represents 1 q (Internal Leaf x Leaf) l (ms_singleton x)

#push-options "--z3rlimit 50 --fuel 1 --ifuel 1"
let rec join_represents (depth:nat) (p q:list tree) (c:tree)
  (lp lq lc:ms)
  : Lemma
      (requires
         0 < depth /\
         is_ith_tail depth p /\
         is_ith_tail depth q /\
         (Leaf? c \/ is_pow2heap depth c) /\
         p `repr` lp /\
         q `repr` lq /\
         c `repr_t` lc)
      (ensures join depth p q c `repr` ms_append lp (ms_append lq lc))
      (decreases p) =

  match p, q, c with
  | [], _, Leaf
  | _, [], Leaf -> ()
  | [], _, _ -> carry_represents depth q c lq lc
  | _, [], _ -> carry_represents depth p c lp lc

  | Leaf::tl_p, Leaf::tl_q, _ ->
    join_represents (depth + 1) tl_p tl_q Leaf
      (keys tl_p) (keys tl_q) ms_empty

  | hd_p::tl_p, Leaf::tl_q, Leaf ->
    join_represents (depth + 1) tl_p tl_q Leaf
      (keys tl_p) (keys tl_q) ms_empty
  | Leaf::tl_p, hd_q::tl_q, Leaf ->
    join_represents (depth + 1) tl_p tl_q Leaf
      (keys tl_p) (keys tl_q) ms_empty
  | Leaf::tl_p, hd_q::tl_q, _ ->
    smash_represents depth hd_q c (keys_of_tree hd_q) (keys_of_tree c);
    join_represents (depth + 1) tl_p tl_q (smash depth hd_q c)
      (keys tl_p) (keys tl_q)
      (ms_append (keys_of_tree hd_q) (keys_of_tree c))

  | hd_p::tl_p, Leaf::tl_q, _ ->
    smash_represents depth hd_p c (keys_of_tree hd_p) (keys_of_tree c);
    join_represents (depth + 1) tl_p tl_q (smash depth hd_p c)
      (keys tl_p) (keys tl_q)
      (ms_append (keys_of_tree hd_p) (keys_of_tree c))

  | hd_p::tl_p, hd_q::tl_q, c ->
    smash_represents depth hd_p hd_q (keys_of_tree hd_p) (keys_of_tree hd_q);
    join_represents (depth + 1) tl_p tl_q (smash depth hd_p hd_q)
      (keys tl_p) (keys tl_q)
      (ms_append (keys_of_tree hd_p) (keys_of_tree hd_q))
#pop-options

let merge (p q:priq) : priq =
  let l = join 1 p q Leaf in
  mk_compact l

let merge_representation (p q:priq) (lp lq:ms)
  : Lemma
      (requires p `repr` lp /\ q `repr` lq)
      (ensures merge p q `repr` (ms_append lp lq)) =

  join_represents 1 p q Leaf lp lq ms_empty

let rec last_key_in_keys (l:list tree)
  : Lemma
      (requires
         Cons? l /\
         Internal? (L.last l))
      (ensures (let Internal _ k _ = L.last l in
                S.subset (S.singleton k) (keys l).ms_elems)) =
  match l with
  | [Internal _ _ _] -> ()
  | _::tl -> last_key_in_keys tl

let rec find_max_some_is_some (k:key_t) (l:list tree)
  : Lemma (ensures Some? (find_max (Some k) l))
          (decreases l) =
  match l with
  | [] -> ()
  | Leaf::tl -> find_max_some_is_some k tl
  | (Internal _ k' _)::tl ->
    if k < k'
    then find_max_some_is_some k' tl
    else find_max_some_is_some k tl

let find_max_emp_repr_l (l:priq)
  : Lemma
      (requires l `repr` ms_empty)
      (ensures find_max None l == None) =
  match l with
  | [] -> ()
  | _ -> last_key_in_keys l

let rec find_max_emp_repr_r (l:list tree)
  : Lemma
      (requires find_max None l == None)
      (ensures permutation (keys l) ms_empty) =
  match l with
  | [] -> ()
  | Leaf::tl -> find_max_emp_repr_r tl
  | (Internal _ k _)::tl -> find_max_some_is_some k tl

let delete_max_none_repr_l (l:priq)
  : Lemma
      (requires l `repr` ms_empty)
      (ensures delete_max l == None) = find_max_emp_repr_l l

let delete_max_none_repr_r (l:priq)
  : Lemma
      (requires delete_max l == None)
      (ensures l `repr` ms_empty) = find_max_emp_repr_r l

let keys_non_emp (x:key_t) (l:list tree)
  : Lemma
      (requires S.mem x (keys l).ms_elems)
      (ensures Cons? l) = ()

let rec keys_append (l1 l2:list tree) (ms1 ms2:ms)
  : Lemma (requires l1 `repr` ms1 /\ l2 `repr` ms2)
          (ensures (L.append l1 l2) `repr` (ms_append ms1 ms2))
          [SMTPat (L.append l1 l2); SMTPat (l1 `repr` ms1); SMTPat (l2 `repr` ms2)] =

  match l1 with
  | [] -> ()
  | _::tl -> keys_append tl l2 (keys tl) ms2

let unzip_repr (depth:nat) (upper_bound:key_t) (t:tree) (lt:ms)
  : Lemma
      (requires pow2heap_pred depth upper_bound t)
      (ensures permutation lt (keys (unzip depth upper_bound t)))
      (decreases t) = ()

  

let heap_delete_max_repr (depth:pos) (t:tree) (lt:ms)
  : Lemma
      (requires
         is_pow2heap depth t /\
         t `repr_t` lt)
      (ensures (
         let Internal left k Leaf = t in
         permutation lt (ms_append (ms_singleton k) (keys (heap_delete_max depth t))))) =

  admit ()
    
let rec delete_max_aux_repr (m:key_t) (depth:pos) (q:list tree)
  (x:key_t) (r:list tree) (p:priq)
  (lq lr lp:ms)
  : Lemma
      (requires
         S.mem m (keys q).ms_elems /\
         is_ith_tail depth q /\
         q `repr` lq /\
         delete_max_aux m depth q == (x, r, p) /\
         r `repr` lr /\
         p `repr` lp)
      (ensures
         permutation lq (ms_append (ms_singleton x)
                                   (ms_append lr lp)))
      (decreases q) =

  match q with
  | [] -> ()
  | Leaf::q ->
    delete_max_aux_repr m (depth + 1) q x (L.tl r) p lq lr lp
  | (Internal left x right)::q ->
    if x < m
    then begin
      assume (~ (S.mem m (keys_of_tree left).ms_elems));
      assume (~ (S.mem m (keys_of_tree right).ms_elems));
      let y, _, _ = delete_max_aux m (depth + 1) q in
      delete_max_aux_repr m (depth + 1) q y (L.tl r) p (keys q) (keys (L.tl r)) lp
    end
    else heap_delete_max_repr depth (Internal left x right) (keys_of_tree (Internal left x right))

let delete_max_some_repr (p q:priq) (k:key_t) (pl ql:ms)
  : Lemma
      (requires
         p `repr` pl /\
         delete_max p == Some (k, q) /\
         q `repr` ql)
      (ensures
         permutation pl (ms_append (ms_singleton k) ql) /\
         (forall (x:key_t). Set.mem x ql.ms_elems ==> x <= k)) = admit ()

