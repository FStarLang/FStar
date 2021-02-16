module Selectors.Tree.Core

open Steel.SelEffect
open Steel.FractionalPermission

module Mem = Steel.Memory
module R = Steel.Reference
module Spec = FStar.Trees

#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"

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
  =
  admit()

let tree_sel_depends_only_on (#a:Type0) (ptr:t a)
  (m0:Mem.hmem (tree_sl ptr)) (m1:mem{disjoint m0 m1})
  : Lemma (tree_sel_node' ptr m0 == tree_sel_node' ptr (Mem.join m0 m1))
  =
  admit()

let tree_sel_depends_only_on_core (#a:Type0) (ptr:t a)
  (m0:Mem.hmem (tree_sl ptr))
  : Lemma (tree_sel_node' ptr m0 == tree_sel_node' ptr (core_mem m0))
  =
  admit()

let tree_sel_node (#a: Type0) (ptr: t a) : selector (Spec.tree (node a)) (tree_sl ptr) =
  Classical.forall_intro_2 (tree_sel_depends_only_on ptr);
  Classical.forall_intro (tree_sel_depends_only_on_core ptr);
  tree_sel_node' ptr

let tree_sel #a r = fun h -> tree_view (tree_sel_node r h)
