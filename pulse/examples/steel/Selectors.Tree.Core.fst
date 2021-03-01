module Selectors.Tree.Core

open Steel.SelEffect
open Steel.FractionalPermission

module Mem = Steel.Memory
module R = Steel.Reference
module Spec = FStar.Trees

#set-options "--fuel 1 --ifuel 1 --z3rlimit 15"

#push-options "--__no_positivity"
noeq type node (a: Type0) = {
  data: a;
  left: ref (node a);
  right: ref (node a);
}
#pop-options

let get_left #a n = n.left
let get_right #a n = n.right
let get_data #a n = n.data

let mk_node #a data left right = {
  data;
  left;
  right
}

let null_t #a = R.null
let is_null_t #a ptr = R.is_null ptr

let rec tree_sl' (#a: Type0) (ptr: t a) (tree: Spec.tree (node a)) : Tot slprop (decreases tree) =
  match tree with
  | Spec.Leaf -> pure (ptr == null_t)
  | Spec.Node data left right ->
    R.pts_to ptr full_perm data `Mem.star`
    tree_sl' data.left left `Mem.star`
    tree_sl' data.right right `Mem.star`
    pure (ptr =!= null_t)

let tree_sl #a ptr = Mem.h_exists (tree_sl' ptr)

let rec tree_view (#a: Type0) (tree: Spec.tree (node a)) : Tot (Spec.tree a) (decreases tree) =
  match tree with
  | Spec.Leaf -> Spec.Leaf
  | Spec.Node data left right -> Spec.Node (get_data data) (tree_view left) (tree_view right)

let tree_sel_node' (#a: Type0) (ptr: t a) : selector' (Spec.tree (node a)) (tree_sl ptr) =
  fun h -> id_elim_exists (tree_sl' ptr) h

let tree_sl'_witinv (#a: Type0) (ptr: t a) : Lemma(is_witness_invariant (tree_sl' ptr))
  = let rec aux (ptr:t a) (x y:tree (node a)) (m:mem) : Lemma
        (requires interp (tree_sl' ptr x) m /\ interp (tree_sl' ptr y) m)
        (ensures x == y)
        (decreases x)
    = match x with
      | Spec.Leaf -> begin match y with
         | Spec.Leaf -> ()
         | Spec.Node data left right ->
           Mem.pure_interp (ptr == null_t) m;
           Mem.pure_star_interp
             (R.pts_to ptr full_perm data
               `Mem.star` tree_sl' (get_left data) left
               `Mem.star` tree_sl' (get_right data) right)
             (ptr =!= null_t) m;
           Mem.pure_interp (ptr =!= null_t) m

       end
      | Spec.Node data1 left1 right1 -> begin match y with
        | Spec.Leaf ->
           Mem.pure_interp (ptr == null_t) m;
           Mem.pure_star_interp
             (R.pts_to ptr full_perm data1
             `Mem.star` tree_sl' (get_left data1) left1
             `Mem.star` tree_sl' (get_right data1) right1)
             (ptr =!= null_t) m;
           Mem.pure_interp (ptr =!= null_t) m
        | Spec.Node data2 left2 right2 ->
           R.pts_to_witinv ptr full_perm;
           aux (get_left data1) left1 left2 m;
           aux (get_right data1) right1 right2 m
      end

    in Classical.forall_intro_3 (Classical.move_requires_3 (aux ptr))

let tree_sel_depends_only_on (#a:Type0) (ptr:t a)
  (m0:Mem.hmem (tree_sl ptr)) (m1:mem{disjoint m0 m1})
  : Lemma (tree_sel_node' ptr m0 == tree_sel_node' ptr (Mem.join m0 m1))
  = let m':Mem.hmem (tree_sl ptr) = Mem.join m0 m1 in
    let t1 = Ghost.reveal (id_elim_exists (tree_sl' ptr) m0) in
    let t2 = Ghost.reveal (id_elim_exists (tree_sl' ptr) m') in

    tree_sl'_witinv ptr;
    Mem.elim_wi (tree_sl' ptr) t1 t2 m'

let tree_sel_depends_only_on_core (#a:Type0) (ptr:t a)
  (m0:Mem.hmem (tree_sl ptr))
  : Lemma (tree_sel_node' ptr m0 == tree_sel_node' ptr (core_mem m0))
  = let t1 = Ghost.reveal (id_elim_exists (tree_sl' ptr) m0) in
    let t2 = Ghost.reveal (id_elim_exists (tree_sl' ptr) (core_mem m0)) in
    tree_sl'_witinv ptr;
    Mem.elim_wi (tree_sl' ptr) t1 t2 (core_mem m0)

let tree_sel_node (#a: Type0) (ptr: t a) : selector (Spec.tree (node a)) (tree_sl ptr) =
  Classical.forall_intro_2 (tree_sel_depends_only_on ptr);
  Classical.forall_intro (tree_sel_depends_only_on_core ptr);
  tree_sel_node' ptr

let tree_sel #a r = fun h -> tree_view (tree_sel_node r h)

let tree_sel_interp (#a: Type0) (ptr: t a) (t: tree (node a)) (m: mem) : Lemma
  (requires interp (tree_sl' ptr t) m)
  (ensures interp (tree_sl ptr) m /\ tree_sel_node' ptr m == t)
  = intro_h_exists t (tree_sl' ptr) m;
    tree_sl'_witinv ptr

let intro_leaf_lemma (a:Type0) (m:mem) : Lemma
    (requires interp (hp_of vemp) m)
    (ensures interp (tree_sl (null_t #a)) m /\ tree_sel (null_t #a) m == Spec.Leaf)
    = let ptr:t a = null_t in
      pure_interp (ptr == null_t) m;
      let open FStar.Tactics in
      assert (tree_sl' ptr Spec.Leaf == pure (ptr == null_t)) by (norm [delta; zeta; iota]);
      tree_sel_interp ptr Spec.Leaf m

let intro_linked_tree_leaf #a _ =
    change_slprop_2 vemp (linked_tree (null_t #a)) (Spec.Leaf <: tree a) (intro_leaf_lemma a)

let elim_leaf_lemma (#a:Type0) (ptr:t a) (m:mem) : Lemma
    (requires interp (tree_sl ptr) m /\ ptr == null_t)
    (ensures interp (tree_sl ptr) m /\ tree_sel ptr m == Spec.Leaf)
    = let l' = id_elim_exists (tree_sl' ptr) m in
      pure_interp (ptr == null_t) m;
      tree_sel_interp ptr Spec.Leaf m

let elim_linked_tree_leaf #a ptr =
  change_slprop_rel (linked_tree ptr) (linked_tree ptr)
    (fun x y -> x == y /\ y == Spec.Leaf)
    (fun m -> elim_leaf_lemma ptr m)

open FStar.Ghost

let lemma_node_not_null (#a:Type) (ptr:t a) (t:tree a) (m:mem) : Lemma
    (requires interp (tree_sl ptr) m /\ tree_sel ptr m == t /\ Spec.Node? t)
    (ensures ptr =!= null_t)
    = let t' = id_elim_exists (tree_sl' ptr) m in
      assert (interp (tree_sl' ptr t') m);
      tree_sel_interp ptr t' m;
      match reveal t' with
      | Spec.Node data left right ->
          let p = (R.pts_to ptr full_perm (hide data)
             `Mem.star` tree_sl' (get_left data) left
             `Mem.star` tree_sl' (get_right data) right) in
          pure_star_interp p (ptr =!= null_t) m

let node_is_not_null #a ptr =
  let h = get #(linked_tree ptr)  () in
  let t = hide (v_linked_tree ptr h) in
  extract_info (linked_tree ptr) t (ptr =!= null_t) (lemma_node_not_null ptr t)

let pack_tree_lemma_aux (#a:Type0) (pt:t a)
  (x: node a) (l r:tree (node a)) (m:mem) : Lemma
  (requires
    interp (R.pts_to pt full_perm x `Mem.star`
      tree_sl' (get_left x) l `Mem.star`
      tree_sl' (get_right x) r)
    m)
  (ensures interp (tree_sl' pt (Spec.Node x l r)) m)
  = affine_star (R.pts_to pt full_perm x `Mem.star` tree_sl' (get_left x) l)
                (tree_sl' (get_right x) r)
                m;
    affine_star (R.pts_to pt full_perm x) (tree_sl' (get_left x) l) m;

    R.pts_to_not_null pt full_perm x m;

    emp_unit (R.pts_to pt full_perm x `Mem.star`
      tree_sl' (get_left x) l `Mem.star`
      tree_sl' (get_right x) r);
    pure_star_interp (R.pts_to pt full_perm x `Mem.star`
      tree_sl' (get_left x) l `Mem.star`
      tree_sl' (get_right x) r)
      (pt =!= null_t)
      m

let pack_tree_lemma (#a:Type0) (pt left right:t a)
  (x: node a) (l r:tree a) (m:mem) : Lemma
  (requires interp (ptr pt `Mem.star` tree_sl left `Mem.star` tree_sl right) m /\
    get_left x == left /\ get_right x == right /\
    sel_of (vptr pt) m == x /\
    sel_of (linked_tree left) m == l /\
    sel_of (linked_tree right) m == r)
  (ensures interp (tree_sl pt) m /\ tree_sel pt m == Spec.Node (get_data x) l r)
  = let l' = id_elim_exists (tree_sl' left) m in
    let r' = id_elim_exists (tree_sl' right) m in
    let aux (m:mem) (ml1 ml2 mr:mem) : Lemma
      (requires disjoint ml1 ml2 /\ disjoint (join ml1 ml2) mr /\ m == join (join ml1 ml2) mr /\
        interp (ptr pt) ml1 /\
        interp (tree_sl left) ml2 /\
        interp (tree_sl right) mr /\

        interp (tree_sl' left l') m /\
        interp (tree_sl' right r') m /\
        ptr_sel pt ml1 == x
      )
      (ensures interp
        (R.pts_to pt full_perm x `Mem.star`
         tree_sl' left l' `Mem.star`
         tree_sl' right r')
       m)
      = ptr_sel_interp pt ml1;

        let l2 = id_elim_exists (tree_sl' left) ml2 in
        join_commutative ml1 ml2;
        assert (interp (tree_sl' left l2) m);
        tree_sl'_witinv left;
        assert (l2 == l');
        assert (interp (tree_sl' left l') ml2);

        let r2 = id_elim_exists (tree_sl' right) mr in
        join_commutative (join ml1 ml2) mr;
        assert (interp (tree_sl' right r2) m);
        tree_sl'_witinv right;
        assert (r2 == r');
        assert (interp (tree_sl' right r') mr);

        intro_star (R.pts_to pt full_perm x) (tree_sl' left l') ml1 ml2;
        intro_star
          (R.pts_to pt full_perm x `Mem.star` tree_sl' left l')
          (tree_sl' right r')
          (join ml1 ml2) mr
    in
    elim_star (ptr pt `Mem.star` tree_sl left) (tree_sl right) m;
    Classical.forall_intro (Classical.move_requires
      (elim_star (ptr pt) (tree_sl left)));
    Classical.forall_intro_3 (Classical.move_requires_3 (aux m));
    pack_tree_lemma_aux pt x l' r' m;
    intro_h_exists (Spec.Node x l' r') (tree_sl' pt) m;
    tree_sel_interp pt (Spec.Node x l' r') m

let pack_tree #a ptr left right =
  let h = get () in
  let x = hide (sel ptr h) in
  let l = hide (v_linked_tree left h) in
  let r = hide (v_linked_tree right h) in
  reveal_star_3 (vptr ptr) (linked_tree left) (linked_tree right);

  change_slprop (vptr ptr `star` linked_tree left `star` linked_tree right) (linked_tree ptr)
    ((reveal x, reveal l), reveal r) (Spec.Node (get_data x) l r)
    (fun m -> pack_tree_lemma ptr left right x l r m)


let unpack_tree #a ptr = sladmit()
