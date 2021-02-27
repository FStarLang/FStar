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
