module Selectors.Tree

open Selectors.Tree.Core
open Steel.Memory
open Steel.SelEffect

module Spec = FStar.Trees

#set-options "--fuel 1 --ifuel 1 --z3rlimit 30"

let rec append_left #a ptr v =
  if is_null_t ptr then (
    drop_linked_tree_leaf ptr;
    let node = mk_node v null_t null_t in
    let new_tree = alloc node in
    intro_linked_tree_leaf #a ();
    intro_linked_tree_leaf #a ();
    pack_tree new_tree null_t null_t;
    new_tree
  ) else (
    let node = unpack_tree ptr in
    let new_left = append_left (get_left node) v in
    let new_node = mk_node (get_data node) new_left (get_right node) in
    write ptr new_node;
    pack_tree ptr new_left (get_right node);
    ptr
  )

let rec append_right #a ptr v =
  if is_null_t ptr then (
    drop_linked_tree_leaf ptr;
    let node = mk_node v null_t null_t in
    let new_tree = alloc node in
    intro_linked_tree_leaf #a ();
    intro_linked_tree_leaf #a ();
    pack_tree new_tree null_t null_t;
    new_tree
  ) else (
    let node = unpack_tree ptr in
    let new_right = append_right (get_right node) v in
    let new_node = mk_node (get_data node) (get_left node) new_right in
    write ptr new_node;
    pack_tree ptr (get_left node) new_right;
    ptr
  )

let rec height #a ptr =
   if is_null_t ptr then (
     elim_linked_tree_leaf ptr; 0
   ) else (
     let node = unpack_tree ptr in
     let hleft = height (get_left node) in
     let hright = height (get_right node) in
     pack_tree ptr (get_left node) (get_right node);
     if hleft > hright then (
       hleft + 1
     ) else ( hright + 1 )
   )

let rec member ptr v =
  if is_null_t ptr then (
    elim_linked_tree_leaf ptr; false
  ) else (
    let node = unpack_tree ptr in
    if v = get_data node then (pack_tree ptr (get_left node) (get_right node); true)
    else (
      let mleft = member (get_left node) v in
      let mright = member (get_right node) v in
      pack_tree ptr (get_left node) (get_right node);
      mleft || mright
    )
  )
assume val sladmit (#a:Type)
            (#[@@@framing_implicit] p:pre_t)
            (#[@@@framing_implicit] q:post_t a)
            (_:unit)
  : SteelSelF a p q (requires fun _ -> True) (ensures fun _ _ _ -> False)

#push-options "--ifuel 1 --fuel 2"
let rotate_left #a ptr =
  let h = get #(linked_tree ptr) () in
  if is_null_t ptr then (
    elim_linked_tree_leaf ptr;
    assert(Spec.rotate_left (v_linked_tree ptr h) == None);
    assert(False);
    noop ();
    ptr
  ) else (
    let x_node = unpack_tree ptr in
    let x = get_data x_node in
    if is_null_t (get_right x_node) then (
      elim_linked_tree_leaf (get_right x_node);
      assert(Spec.rotate_left (v_linked_tree ptr h) == None);
      assert(False);
      pack_tree ptr (get_left x_node) (get_right x_node);
      ptr
    ) else (
      let z_node = unpack_tree (get_right x_node) in
      let z = get_data z_node in
      let new_subnode = mk_node x (get_left x_node) (get_left z_node) in
      let new_node = mk_node z ptr (get_right z_node) in
      write (get_right x_node) new_node;
      write ptr new_subnode;
      pack_tree ptr (get_left x_node) (get_left z_node);
      pack_tree (get_right x_node) ptr (get_right z_node);
      (get_right x_node)
    )
  )
#pop-options
