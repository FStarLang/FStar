(*
   Copyright 2022 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.

   Authors: Aseem Rastogi
*)

module BinomialQueue

module L = FStar.List.Tot

/// Some auxiliary lemmas

let rec last_cons (#a:Type) (x:a) (l:list a)
  : Lemma
      (requires Cons? l)
      (ensures L.last (x::l) == L.last l)
      [SMTPat (L.last (x::l))] =

  match l with
  | [_] -> ()
  | _::tl -> last_cons x tl


/// We will maintain the priority queue as a forest

type tree =
  | Leaf : tree
  | Internal : tree -> key_t -> tree -> tree

/// Tree t is a complete binary tree of depth d
///
/// All its keys are <= upper_bound
///
/// If the left subtree is non-empty,
///   its root is maximum in its subtree

let rec pow2heap_pred (d:nat) (upper_bound:key_t) (t:tree) : prop =
  match t with
  | Leaf -> d == 0
  | Internal left k right ->
    0 < d /\
    k <= upper_bound /\
    pow2heap_pred (d - 1) k left /\
    pow2heap_pred (d - 1) upper_bound right

/// A power-2-heap of depth d is an Internal tree whose right child is a Leaf,
///   and left child is a complete binary tree satisfying pow2heap_pred
///   with upper bound as the key k

let is_pow2heap (d:pos) (t:tree) : prop =
  match t with
  | Internal left k Leaf -> pow2heap_pred (d - 1) k left
  | _ -> False

/// A list of trees is a binomial queue starting with depth d if:

let rec is_binomial_queue (d:pos) (l:list tree)
  : Tot prop (decreases l) =
  
  match l with
  | [] -> True
  | hd::tl ->
    (Leaf? hd \/ is_pow2heap d hd) /\ is_binomial_queue (d + 1) tl

/// We will also keep the binomial queue in a compact form,
///   truncating unnecessary empty trees from the forest

let is_compact (l:list tree) = l == [] \/ Internal? (L.last l)

let is_priq (l:list tree) = is_binomial_queue 1 l /\ is_compact l

/// The main priq type

let priq = l:list tree{is_priq l}

let empty = []

/// We define a function to compact a forest

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

/// Correctness of mk_compact

let rec mk_compact_correctness (l:list tree)
  : Lemma (is_compact (mk_compact l))
          [SMTPat (is_compact (mk_compact l))] =

  match l with
  | [] -> ()
  | _ ->
    if all_leaf l then ()
    else mk_compact_correctness (L.tl l)

let rec mk_compact_preserves_binomial_queue (d:pos) (l:list tree)
  : Lemma
      (requires is_binomial_queue d l)
      (ensures is_binomial_queue d (mk_compact l))
      (decreases l)
      [SMTPat (is_binomial_queue d (mk_compact l))] =
  match l with
  | [] -> ()
  | _ ->
    if all_leaf l then ()
    else mk_compact_preserves_binomial_queue (d + 1) (L.tl l)

/// smash is a key function combining two power of 2 heaps of depth d
///   into a power of 2 heap of depth (d + 1)

let smash (d:pos) (t1:tree) (t2:tree)
  : Pure tree
         (requires is_pow2heap d t1 /\ is_pow2heap d t2)
         (ensures fun t -> is_pow2heap (d + 1) t) =

  match t1, t2 with
  | Internal left1 k1 Leaf, Internal left2 k2 Leaf ->
    if k1 <= k2
    then Internal (Internal left1 k1 left2) k2 Leaf
    else Internal (Internal left2 k2 left1) k1 Leaf

/// carry adds t to q, preserving the binomial queue relation
///
/// It has a nice symmetery to carry in binary arithmetic

let rec carry (d:pos) (q:list tree) (t:tree)
  : Pure (list tree)
         (requires is_binomial_queue d q /\ is_pow2heap d t)
         (ensures fun q -> is_binomial_queue d q)
         (decreases q) =
  match q with
  | [] -> [t]
  | Leaf::tl -> t::tl
  | hd::tl ->
    let q = carry (d + 1) tl (smash d hd t) in
    Leaf::q

/// join combines two trees p and q, with the carry c,
///   preserving the binomial queue relation
///
/// It has a nice symmetry to binary addition

let rec join (d:pos) (p q:list tree) (c:tree)
  : Pure (list tree)
         (requires
            is_binomial_queue d p /\
            is_binomial_queue d q /\
            (Leaf? c \/ is_pow2heap d c))
         (ensures fun q -> is_binomial_queue d q)
         (decreases L.length p) =

  match p, q, c with
  | [], _, Leaf -> q
  | _, [], Leaf -> p
  | [], _, _ -> carry d q c
  | _, [], _ -> carry d p c
  | Leaf::tl_p, Leaf::tl_q, _ ->
    c::(join (d + 1) tl_p tl_q Leaf)
  | hd_p::tl_p, Leaf::tl_q, Leaf ->
    hd_p::(join (d + 1) tl_p tl_q Leaf)
  | Leaf::tl_p, hd_q::tl_q, Leaf ->
    hd_q::(join (d + 1) tl_p tl_q Leaf)
  | Leaf::tl_p, hd_q::tl_q, _ ->
    Leaf::(join (d + 1) tl_p tl_q (smash d hd_q c))
  | hd_p::tl_p, Leaf::tl_q, _ ->
    Leaf::(join (d + 1) tl_p tl_q (smash d hd_p c))
  | hd_p::tl_p, hd_q::tl_q, c ->
    c::(join (d + 1) tl_p tl_q (smash d hd_p hd_q))

/// insert is just carry of (Internal Leaf x Leaf) to q

let insert x q =
  let l = carry 1 q (Internal Leaf x Leaf) in
  mk_compact l


/// Towards delete max


/// find_max with the current max as max

let rec find_max (max:option key_t) (q:list tree)
  : Tot (option key_t) (decreases q) =
  match q with
  | [] -> max
  | Leaf::q -> find_max max q
  | (Internal _ k _)::q ->
    match max with
    | None -> find_max (Some k) q
    | Some max -> find_max (if max < k then Some k else Some max) q


/// If q is a binomial queue starting at depth d,
///   and t is a power of 2 heap of depth (d + length q)
///
/// Then appending t to q is also a binomial queue

let rec binomial_queue_append (d:pos) (q:list tree) (t:tree)
  : Lemma
      (requires
         is_binomial_queue d q /\ is_pow2heap (L.length q + d) t)
      (ensures is_binomial_queue d (L.append q [t]))
      (decreases q) =
  match q with
  | [] -> ()
  | _::q -> binomial_queue_append (d + 1) q t


/// unzip splits the tree t along its right spine
///
/// See https://www.cs.princeton.edu/~appel/BQ.pdf
///
/// The upper bound is only needed to show we return a priq,
///   may be it's not important?

let rec unzip (d:nat) (upper_bound:key_t) (t:tree)
  : Pure priq
         (requires pow2heap_pred d upper_bound t)
         (ensures fun q -> L.length q == d) =

  match t with
  | Leaf -> []
  | Internal left k right ->
    let q = unzip (d - 1) upper_bound right in
    binomial_queue_append 1 q (Internal left k Leaf);
    L.append_length q [Internal left k Leaf];
    L.lemma_append_last q [Internal left k Leaf];
    L.append q [Internal left k Leaf]

/// Delete root of t, and unzip it

let heap_delete_max (d:pos) (t:tree)
  : Pure priq
         (requires is_pow2heap d t)
         (ensures fun q -> L.length q == d - 1) =

  match t with
  | Internal left k Leaf -> unzip (d - 1) k left

/// Take the first tree in q whose root is >= m,
///   delete its root and unzip it,
///   return (the deleted root, q with that tree replaces with Leaf, unzipped forest)
/// 

let rec delete_max_aux (m:key_t) (d:pos) (q:list tree)
  : Pure (key_t & list tree & priq)
         (requires is_binomial_queue d q)
         (ensures fun (x, q, _) -> m <= x /\ is_binomial_queue d q)
         (decreases q) =

  match q with
  | [] -> m + 1, [], []  // this case won't arise
                         // we could strengthen preconditions
  | Leaf::q ->
    let x, q, new_q = delete_max_aux m (d + 1) q in
    x, Leaf::q, new_q
  | (Internal left x right)::q ->
    if x < m
    then let y, q, new_q = delete_max_aux m (d + 1) q in
         y, (Internal left x right)::q, new_q
    else x, Leaf::q, heap_delete_max d (Internal left x right)

/// delete_max finds the maximum key in the forest,
///   deletes it from its tree, and joins the remaining forests

let delete_max q =
  match find_max None q with
  | None -> None
  | Some m ->
    let x, q, new_q = delete_max_aux m 1 q in
    let r = join 1 q new_q Leaf in
    mk_compact_correctness r;
    Some (x, mk_compact r)

/// merge is just join with Leaf as the carry

let merge p q =
  let l = join 1 p q Leaf in
  mk_compact l

/// Towards defining repr

let rec keys_of_tree (t:tree) : ms =
  match t with
  | Leaf -> ms_empty
  | Internal left k right ->
    ms_append (keys_of_tree left)
              (ms_cons k (keys_of_tree right))

let rec keys (q:list tree) : ms =
  match q with
  | [] -> ms_empty
  | hd::tl -> ms_append (keys_of_tree hd) (keys tl)

let repr_t (t:tree) (l:ms) : prop =
  permutation (keys_of_tree t) l

let repr_l (q:list tree) (s:ms) : prop =
  permutation (keys q) s

/// The main repr predicate saying s is a permutation of (keys q)

let repr q s = repr_l q s

let empty_repr _ = ()

/// Correctness of carry and join

let smash_repr (d:pos) (t1 t2:tree) (l1 l2:ms)
  : Lemma
      (requires
         is_pow2heap d t1 /\
         is_pow2heap d t2 /\
         t1 `repr_t` l1 /\
         t2 `repr_t` l2)
      (ensures smash d t1 t2 `repr_t` (ms_append l1 l2)) = ()

let rec carry_repr (d:pos) (q:list tree) (t:tree) (lq lt:ms)
  : Lemma
      (requires
         is_binomial_queue d q /\
         is_pow2heap d t /\
         q `repr_l` lq /\
         t `repr_t` lt)
      (ensures carry d q t `repr_l` ms_append lq lt)
      (decreases q) =

  match q with
  | [] -> ()
  | Leaf::_ -> ()
  | hd::tl ->
    smash_repr d hd t (keys_of_tree hd) (keys_of_tree t);
    carry_repr (d + 1) tl (smash d hd t)
      (keys tl)
      (ms_append (keys_of_tree hd) (keys_of_tree t))

#push-options "--z3rlimit 50 --fuel 1 --ifuel 1"
let rec join_repr (d:pos) (p q:list tree) (c:tree)
  (lp lq lc:ms)
  : Lemma
      (requires
         is_binomial_queue d p /\
         is_binomial_queue d q /\
         (Leaf? c \/ is_pow2heap d c) /\
         p `repr_l` lp /\
         q `repr_l` lq /\
         c `repr_t` lc)
      (ensures join d p q c `repr_l` ms_append lp (ms_append lq lc))
      (decreases p) =

  match p, q, c with
  | [], _, Leaf
  | _, [], Leaf -> ()
  | [], _, _ -> carry_repr d q c lq lc
  | _, [], _ -> carry_repr d p c lp lc

  | Leaf::tl_p, Leaf::tl_q, _ ->
    join_repr (d + 1) tl_p tl_q Leaf
      (keys tl_p) (keys tl_q) ms_empty

  | hd_p::tl_p, Leaf::tl_q, Leaf ->
    join_repr (d + 1) tl_p tl_q Leaf
      (keys tl_p) (keys tl_q) ms_empty
  | Leaf::tl_p, hd_q::tl_q, Leaf ->
    join_repr (d + 1) tl_p tl_q Leaf
      (keys tl_p) (keys tl_q) ms_empty
  | Leaf::tl_p, hd_q::tl_q, _ ->
    smash_repr d hd_q c (keys_of_tree hd_q) (keys_of_tree c);
    join_repr (d + 1) tl_p tl_q (smash d hd_q c)
      (keys tl_p) (keys tl_q)
      (ms_append (keys_of_tree hd_q) (keys_of_tree c))

  | hd_p::tl_p, Leaf::tl_q, _ ->
    smash_repr d hd_p c (keys_of_tree hd_p) (keys_of_tree c);
    join_repr (d + 1) tl_p tl_q (smash d hd_p c)
      (keys tl_p) (keys tl_q)
      (ms_append (keys_of_tree hd_p) (keys_of_tree c))

  | hd_p::tl_p, hd_q::tl_q, c ->
    smash_repr d hd_p hd_q (keys_of_tree hd_p) (keys_of_tree hd_q);
    join_repr (d + 1) tl_p tl_q (smash d hd_p hd_q)
      (keys tl_p) (keys tl_q)
      (ms_append (keys_of_tree hd_p) (keys_of_tree hd_q))
#pop-options

/// mk_compact preserves keys

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

/// insert and merge correctness follows from carry and joinx

let insert_repr x q s =
  carry_repr 1 q (Internal Leaf x Leaf) s (ms_singleton x)

let merge_repr p q sp sq =
  join_repr 1 p q Leaf sp sq ms_empty

/// Towards proof of delete correctness

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
  : Lemma (ensures Some? (find_max (Some k) l) /\
                   k <= Some?.v (find_max (Some k) l))
          (decreases l) =
  match l with
  | [] -> ()
  | Leaf::tl -> find_max_some_is_some k tl
  | (Internal _ k' _)::tl ->
    let k = if k < k' then k' else k in
    find_max_some_is_some k tl

let find_max_emp_repr_l (l:priq)
  : Lemma
      (requires l `repr_l` ms_empty)
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


#push-options "--warn_error -271"
let delete_max_none_repr p =
  let delete_max_none_repr_l (l:priq)
    : Lemma
        (requires l `repr` ms_empty)
        (ensures delete_max l == None)
        [SMTPat ()] = find_max_emp_repr_l l in

  let delete_max_none_repr_r (l:priq)
    : Lemma
        (requires delete_max l == None)
        (ensures l `repr` ms_empty)
        [SMTPat ()] = find_max_emp_repr_r l in
  ()
#pop-options
  
let rec keys_append (l1 l2:list tree) (ms1 ms2:ms)
  : Lemma (requires l1 `repr_l` ms1 /\ l2 `repr_l` ms2)
          (ensures (L.append l1 l2) `repr_l` (ms_append ms1 ms2)) =

  match l1 with
  | [] -> ()
  | _::tl -> keys_append tl l2 (keys tl) ms2

let rec unzip_repr (d:nat) (upper_bound:key_t) (t:tree) (lt:ms)
  : Lemma
      (requires
         pow2heap_pred d upper_bound t /\
         permutation (keys_of_tree t) lt)
      (ensures permutation lt (keys (unzip d upper_bound t)))
      (decreases t) =
  match t with
  | Leaf -> ()
  | Internal left k right ->
    let q = unzip (d - 1) upper_bound right in
    unzip_repr (d - 1) upper_bound right (keys_of_tree right);
    keys_append q [Internal left k Leaf]
      (keys_of_tree right) (ms_append (keys_of_tree left)
                                      (ms_append (ms_singleton k)
                                                 ms_empty))

let heap_delete_max_repr (d:pos) (t:tree) (lt:ms)
  : Lemma
      (requires is_pow2heap d t /\ t `repr_t` lt)
      (ensures (
         let Internal left k Leaf = t in
         permutation lt (ms_append (ms_singleton k)
                                   (keys (heap_delete_max d t))))) =

  let Internal left k Leaf = t in
  unzip_repr (d - 1) k left (keys_of_tree left)

let max (k:key_t) (s:S.set key_t) =
  forall (x:key_t). Set.mem x s ==> x <= k

let rec tree_root_is_max_aux (d:nat) (upper_bound:key_t) (t:tree)
  : Lemma
      (requires pow2heap_pred d upper_bound t)
      (ensures max upper_bound (keys_of_tree t).ms_elems)
      (decreases t) =

  match t with
  | Leaf -> ()
  | Internal left k right ->
    tree_root_is_max_aux (d - 1) k left;
    tree_root_is_max_aux (d - 1) upper_bound right

let tree_root_is_max (d:pos) (t:tree)
  : Lemma
      (requires is_pow2heap d t)
      (ensures
         (let Internal left k Leaf = t in
          max k (keys_of_tree left).ms_elems)) =
  let Internal left k Leaf = t in
  tree_root_is_max_aux (d - 1) k left

#push-options "--z3rlimit 40"
let rec delete_max_aux_repr (m:key_t) (d:pos) (q:list tree)
  (x:key_t) (r:list tree) (p:priq)
  (lq lr lp:ms)
  : Lemma
      (requires
         S.mem m (keys q).ms_elems /\
         is_binomial_queue d q /\
         q `repr_l` lq /\
         delete_max_aux m d q == (x, r, p) /\
         r `repr_l` lr /\
         p `repr_l` lp)
      (ensures
         permutation lq (ms_append (ms_singleton x)
                                   (ms_append lr lp)))
      (decreases q) =

  match q with
  | [] -> ()
  | Leaf::q ->
    delete_max_aux_repr m (d + 1) q x (L.tl r) p lq lr lp
  | (Internal left x Leaf)::q ->
    if x < m
    then begin
      tree_root_is_max d (Internal left x Leaf);
      assert (~ (S.mem m (keys_of_tree left).ms_elems));
      let y, _, _ = delete_max_aux m (d + 1) q in
      delete_max_aux_repr m (d + 1) q y (L.tl r) p (keys q) (keys (L.tl r)) lp
    end
    else heap_delete_max_repr d (Internal left x Leaf) (keys_of_tree (Internal left x Leaf))
#pop-options

let rec find_max_mem_keys (kopt:option key_t) (q:list tree)
  : Lemma
      (ensures
         find_max kopt q == kopt \/
         (let kopt = find_max kopt q in
          Some? kopt /\ S.mem (Some?.v kopt) (keys q).ms_elems))
      (decreases q) =
  match q with
  | [] -> ()
  | Leaf::q -> find_max_mem_keys kopt q
  | (Internal _ k _)::q ->
    match kopt with
    | None ->
      find_max_mem_keys (Some k) q
    | Some k' ->
      let k = if k' < k then k else k' in
      find_max_mem_keys (Some k) q

let rec find_max_is_max (d:pos) (kopt:option key_t) (q:list tree)
  : Lemma
      (requires
         is_binomial_queue d q /\
         Some? (find_max kopt q))
      (ensures
         (let Some k = find_max kopt q in
          max k (keys q).ms_elems))
      (decreases q) =
  match q with
  | [] -> ()
  | Leaf::q ->
    find_max_is_max (d + 1) kopt q
  | (Internal left k Leaf)::tl ->
    tree_root_is_max d (Internal left k Leaf);
    match kopt with
    | None ->
      find_max_is_max (d + 1) (Some k) tl;
      find_max_some_is_some k tl
    | Some k' ->
      let k = if k' < k then k else k' in
      find_max_is_max (d + 1) (Some k) tl;
      find_max_some_is_some k tl

let delete_max_some_repr p pl k q ql =
  match find_max None p with
  | None -> ()
  | Some m ->
    find_max_mem_keys None p;
    assert (S.mem m (keys p).ms_elems);
    let x, q, new_q = delete_max_aux m 1 p in
    delete_max_aux_repr m 1 p x q new_q
      pl (keys q) (keys new_q);
    let r = join 1 q new_q Leaf in
    join_repr 1 q new_q Leaf (keys q) (keys new_q) ms_empty;
    compact_preserves_keys r;
    assert (permutation pl (ms_append (ms_singleton k) ql));
    find_max_is_max 1 None p
