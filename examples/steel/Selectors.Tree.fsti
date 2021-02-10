module Selectors.Tree

open Steel.Memory
open Steel.SelEffect

module Spec = FStar.Trees

(*** Type declarations *)

(**** Base types *)

(** A node of the tree *)
val node (a: Type0) : Type

(** A tree is a ref to a node, themselves referencing other nodes *)
let t (a: Type0) = ref (node a)

(** This type reflects the contents of a tree without the memory layout *)
type tree (a: Type0) = Spec.tree a
(**** Slprop and selector *)

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

(**** Operations on nodes *)

val get_left (#a: Type0) (n: node a) : t a
val get_right (#a: Type0) (n: node a) : t a
val get_data (#a: Type0) (n: node a) : a
val mk_node (#a: Type0) (left right: t a) (v: a)
    : Pure (node a)
      (requires True)
      (ensures (fun n -> get_left n == left /\ get_right n == right /\ get_data n == v))

(**** Low-level operations on trees *)

val null_t (#a: Type0) : t a
val is_null_t (#a: Type0) (r: t a) : (b:bool{b <==> r == null_t})

val intro_linked_tree_leaf (#a: Type0)
    : SteelSel unit
      vemp (fun _ -> linked_tree (null_t #a))
      (requires (fun _ -> True))
      (ensures (fun _ _ h1 -> v_linked_tree #a null_t h1 == Spec.Leaf))

val elim_linked_tree_leaf (#a: Type0) (ptr: t a)
    : SteelSel unit
       (linked_tree ptr) (fun _ -> linked_tree ptr)
       (requires (fun _ -> is_null_t ptr))
       (ensures (fun h0 _ h1 ->
         v_linked_tree ptr h0 == v_linked_tree ptr h1 /\
         v_linked_tree ptr h1 == Spec.Leaf))

val pack_tree (#a: Type0) (ptr: t a) (left: t a) (right: t a)
    : SteelSel unit
      (vptr ptr `star` linked_tree left `star` linked_tree right)
      (fun _ -> linked_tree ptr)
      (requires (fun h0 ->
        not (is_null_t ptr) /\
        get_left (sel ptr h0) == left /\
        get_right (sel ptr h0) == right))
      (ensures (fun h0 _ h1 ->
        v_linked_tree ptr h1 ==
          Spec.Node (get_data (sel ptr h0)) (v_linked_tree left h0) (v_linked_tree right h0)
      ))

val unpack_tree (#a: Type0) (ptr: t a)
    : SteelSel (t a & t a)
      (linked_tree ptr)
      (fun (left, right) ->
        linked_tree left `star` linked_tree right `star` vptr ptr)
      (requires (fun h0 -> not (is_null_t ptr)))
      (ensures (fun h0 (left, right) h1 ->
        v_linked_tree ptr h0 == Spec.Node
          (admit())
          // AF: why ({ Spec.key = get_data (sel ptr h1); Spec.payload = get_data (sel ptr h1)})
          (v_linked_tree left h1)
          (v_linked_tree right h1)
      ))

(**** High-level operations on trees *)

val append_left (#a: Type0) (ptr: t a) (v : a)
    : SteelSel (t a)
      (linked_tree ptr)
      (fun ptr' ->  linked_tree ptr')
      (requires (fun h0 -> True))
      (ensures (fun h0 ptr' h1 -> v_linked_tree ptr' h1 == Spec.append_left (v_linked_tree ptr h0) v))

val append_right (#a: Type0) (ptr: t a) (v : a)
    : SteelSel (t a)
      (linked_tree ptr)
      (fun ptr' ->  linked_tree ptr')
      (requires (fun h0 -> True))
      (ensures (fun h0 ptr' h1 ->
        v_linked_tree ptr' h1 == Spec.append_right (v_linked_tree ptr h0) v
      ))
