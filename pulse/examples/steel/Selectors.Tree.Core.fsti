module Selectors.Tree.Core

open Steel.Memory
open Steel.Effect
open Steel.Reference

module Spec = Trees

#set-options "--ide_id_info_off"

(*** Type declarations *)

(**** Base types *)

(** A node of the tree *)
val node (a: Type0) : Type0

(** A tree is a ref to a node, themselves referencing other nodes *)
let t (a: Type0) = ref (node a)

(** This type reflects the contents of a tree without the memory layout *)
let tree (a: Type0) = Spec.tree a

(**** Operations on nodes *)

val get_left (#a: Type0) (n: node a) : t a
val get_right (#a: Type0) (n: node a) : t a
val get_data (#a: Type0) (n: node a) : a
val mk_node (#a: Type0) (data: a) (left right: t a)
    : Pure (node a)
      (requires True)
      (ensures (fun n -> get_left n == left /\ get_right n == right /\ get_data n == data))


(**** Slprop and selector *)

val null_t (#a: Type0) : t a
val is_null_t (#a: Type0) (r: t a) : (b:bool{b <==> r == null_t})


(** The separation logic proposition representing the memory layout of the tree *)
val tree_sl (#a: Type0) (r: t a) : slprop u#1

(** Selector retrieving the contents of a tree in memory *)
val tree_sel (#a: Type0) (r: t a) : selector (tree a) (tree_sl r)

[@@__steel_reduce__]
let linked_tree' (#a: Type0) (r: t a) : vprop' = {
  hp = tree_sl r;
  t = tree a;
  sel = tree_sel r
}

(** The view proposition encapsulating the separation logic proposition and the selector *)
unfold let linked_tree (#a: Type0) (tr: t a) : vprop = VUnit (linked_tree' tr)

(** This convenience helper retrieves the contents of a tree from an [rmem] *)
[@@ __steel_reduce__]
let v_linked_tree
  (#a:Type0)
  (#p:vprop)
  (r:t a)
  (h:rmem p{
    FStar.Tactics.with_tactic selector_tactic (can_be_split p (linked_tree r) /\ True)
  })
    : GTot (tree a)
  = h (linked_tree r)

(*** Operations *)

(**** Low-level operations on trees *)

val intro_linked_tree_leaf (#a: Type0) (_: unit)
    : Steel unit
      emp (fun _ -> linked_tree (null_t #a))
      (requires (fun _ -> True))
      (ensures (fun _ _ h1 -> v_linked_tree #a null_t h1 == Spec.Leaf))

val elim_linked_tree_leaf (#a: Type0) (ptr: t a)
    : Steel unit
       (linked_tree ptr) (fun _ -> linked_tree ptr)
       (requires (fun _ -> is_null_t ptr))
       (ensures (fun h0 _ h1 ->
         v_linked_tree ptr h0 == v_linked_tree ptr h1 /\
         v_linked_tree ptr h1 == Spec.Leaf))

val node_is_not_null (#a: Type0) (ptr: t a)
    : Steel unit
       (linked_tree ptr) (fun _ -> linked_tree ptr)
       (requires (fun h0 -> Spec.Node? (v_linked_tree ptr h0)))
       (ensures (fun h0 _ h1 -> not (is_null_t ptr) /\ v_linked_tree ptr h0 == v_linked_tree ptr h1))

val pack_tree (#a: Type0) (ptr: t a) (left: t a) (right: t a)
    : Steel unit
      (vptr ptr `star` linked_tree left `star` linked_tree right)
      (fun _ -> linked_tree ptr)
      (requires (fun h0 ->
        get_left (sel ptr h0) == left /\
        get_right (sel ptr h0) == right))
      (ensures (fun h0 _ h1 ->
        v_linked_tree ptr h1 ==
          Spec.Node (get_data (sel ptr h0)) (v_linked_tree left h0) (v_linked_tree right h0)
      ))

val unpack_tree (#a: Type0) (ptr: t a)
    : Steel (node a)
      (linked_tree ptr)
      (fun node ->
        linked_tree (get_left node) `star` linked_tree (get_right node) `star` vptr ptr)
      (requires (fun h0 -> not (is_null_t ptr)))
      (ensures (fun h0 node h1 ->
        v_linked_tree ptr h0 == Spec.Node
          (get_data (sel ptr h1))
          (v_linked_tree (get_left node) h1)
          (v_linked_tree (get_right node) h1) /\
        (sel ptr h1) == node
      ))
