module Selectors.Tree

open Selectors.Tree.Core
open Steel.Memory
open Steel.SelEffect

module Spec = Trees

#set-options "--fuel 1 --ifuel 1 --z3rlimit 50 --ide_id_info_off"

let rec append_left #a ptr v =
  if is_null_t ptr then (
    elim_linked_tree_leaf ptr;
    let node = mk_node v ptr null_t in
    let new_tree = alloc node in
    intro_linked_tree_leaf #a ();
    pack_tree new_tree ptr null_t;
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
    elim_linked_tree_leaf ptr;
    let node = mk_node v null_t ptr in
    let new_tree = alloc node in
    intro_linked_tree_leaf #a ();
    pack_tree new_tree null_t ptr;
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

#push-options "--ifuel 1 --fuel 2"
let rotate_left #a ptr =
  let h = get() in
  node_is_not_null ptr;
  let x_node = unpack_tree ptr in
  let x = get_data x_node in
  node_is_not_null (get_right x_node);
  let z_node = unpack_tree (get_right x_node) in
  let z = get_data z_node in
  let new_subnode = mk_node x (get_left x_node) (get_left z_node) in
  let new_node = mk_node z ptr (get_right z_node) in
  write (get_right x_node) new_node;
  write ptr new_subnode;
  pack_tree ptr (get_left x_node) (get_left z_node);
  pack_tree (get_right x_node) ptr (get_right z_node);
  (get_right x_node)

let rotate_right #a ptr =
  let h = get () in
  node_is_not_null ptr;
  let x_node = unpack_tree ptr in
  let x = get_data x_node in
  node_is_not_null (get_left x_node);
  let z_node = unpack_tree (get_left x_node) in
  let z = get_data z_node in
  let new_subnode = mk_node x (get_right z_node) (get_right x_node) in
  let new_node = mk_node z (get_left z_node) ptr in
  write (get_left x_node) new_node;
  write ptr new_subnode;
  pack_tree ptr (get_right z_node) (get_right x_node);
  pack_tree (get_left x_node) (get_left z_node) ptr;
  (get_left x_node)


let rotate_right_left #a ptr =
  let h = get () in
  node_is_not_null ptr;
  // original root node
  let x_node = unpack_tree ptr in
  let x = get_data x_node in
  node_is_not_null (get_right x_node);
  // original right node
  // z = get_right x_node
  let z_node = unpack_tree (get_right x_node) in
  let z = get_data z_node in
  node_is_not_null (get_left z_node);
  // original left (right node)
  // y = get_left (z_node)
  let y_node = unpack_tree (get_left z_node) in
  let y = get_data y_node in
  let new_x = mk_node x (get_left x_node) (get_left y_node) in
  let new_z = mk_node z (get_right y_node) (get_right z_node) in
  let new_y = mk_node y ptr (get_right x_node) in

  write ptr new_x;
  write (get_right x_node) new_z;
  write (get_left z_node) new_y;

  pack_tree ptr (get_left x_node) (get_left y_node);
  pack_tree (get_right x_node) (get_right y_node) (get_right z_node);
  pack_tree (get_left z_node) ptr (get_right x_node);

  (get_left z_node)


let rotate_left_right #a ptr =
  let h = get () in

  node_is_not_null ptr;
  // original root node
  let x_node = unpack_tree ptr in
  let x = get_data x_node in

  node_is_not_null (get_left x_node);

  // original left node
  // z = get_left x_node
  let z_node = unpack_tree (get_left x_node) in
  let z = get_data z_node in

  node_is_not_null (get_right z_node);

  // original right (left node)
  // y = get_right (z_node)
  let y_node = unpack_tree (get_right z_node) in
  let y = get_data y_node in

  let new_z = mk_node z (get_left z_node) (get_left y_node) in
  let new_x = mk_node x (get_right y_node) (get_right x_node) in
  let new_y = mk_node y (get_left x_node) ptr in

  write (get_left x_node) new_z;
  write ptr new_x;
  write (get_right z_node) new_y;

  pack_tree (get_left x_node) (get_left z_node) (get_left y_node);
  pack_tree ptr (get_right y_node) (get_right x_node);
  pack_tree (get_right z_node) (get_left x_node) ptr;

  (get_right z_node)

let rec is_balanced #a ptr =
  if is_null_t ptr then (
    elim_linked_tree_leaf ptr; true
  ) else (

  let node = unpack_tree ptr in
  let lh = height (get_left node) in
  let rh = height (get_right node) in

  let lbal = is_balanced(get_left node) in
  let rbal = is_balanced(get_right node) in

  pack_tree ptr (get_left node) (get_right node);
  (lbal && rbal) && ((rh - lh) >= -1 && (rh - lh) <= 1))

let rebalance_avl #a cmp ptr =
  let h = get () in

  if is_balanced ptr then (
    noop();
    ptr
  ) else (

    node_is_not_null ptr;
    let node = unpack_tree ptr in

    let lh = height (get_left node) in
    let rh = height (get_right node) in

    if (lh - rh) > 1 then (

      node_is_not_null (get_left node);
      let l_node = unpack_tree (get_left node) in

      let llh = height (get_left l_node) in
      let lrh = height (get_right l_node) in

      pack_tree (get_left node) (get_left l_node) (get_right l_node);
      pack_tree ptr (get_left node) (get_right node);

      if lrh > llh then (
        rotate_left_right ptr

      ) else (
        rotate_right ptr
      )

    ) else (

      if (lh - rh) < - 1 then (

        node_is_not_null (get_right node);
        let r_node = unpack_tree (get_right node) in

        let rlh = height (get_left r_node) in
        let rrh = height (get_right r_node) in

        pack_tree (get_right node) (get_left r_node) (get_right r_node);
        pack_tree ptr (get_left node) (get_right node);

        if rlh > rrh then (
            rotate_right_left ptr
        ) else (
            rotate_left ptr
        )

      ) else (
          pack_tree ptr (get_left node) (get_right node);
          ptr
      )
    )
  )

let rec insert_avl #a cmp ptr v =
  if is_null_t ptr then (
    elim_linked_tree_leaf ptr;
    let node = mk_node v ptr null_t in
    let new_tree = alloc node in
    intro_linked_tree_leaf #a ();
    pack_tree new_tree ptr null_t;
    new_tree
  ) else (
    let node = unpack_tree ptr in
    if cmp (get_data node) v >= 0 then (
      let new_left = insert_avl cmp (get_left node) v in
      let new_node = mk_node (get_data node) new_left (get_right node) in
      write ptr new_node;
      pack_tree ptr new_left (get_right node);
      rebalance_avl cmp ptr
    )
    else (
      let new_right = insert_avl cmp (get_right node) v in
      let new_node = mk_node (get_data node) (get_left node) new_right in
      write ptr new_node;
      pack_tree ptr (get_left node) new_right;
      rebalance_avl cmp ptr
    )
  )

#pop-options
