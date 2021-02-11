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
    assume(not(is_null_t new_tree));
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
