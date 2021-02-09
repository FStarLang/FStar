module Selectors.Tree

open Steel.Memory
open Steel.SelEffect

(*** Type declarations *)

(**** Base types *)

(** A node of the tree *)
val node (a: Type0) : Type

(** A tree is a ref to a node, themselves referencing other nodes *)
let t (a: Type0) = ref (node a)

(** This type reflects the contents of a tree without the memory layout *)
type tree (a: Type0) =
  | Leaf : tree a
  | Node: data: a -> left: tree a -> right: tree a -> tree a

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
      (ensures (fun _ _ h1 -> v_linked_tree #a null_t h1 == Leaf))

val elim_linked_tree_leaf (#a: Type0) (ptr: t a)
    : SteelSel unit
       (linked_tree ptr) (fun _ -> linked_tree ptr)
       (requires (fun _ -> is_null_t ptr))
       (ensures (fun h0 _ h1 ->
         v_linked_tree ptr h0 == v_linked_tree ptr h1 /\
         v_linked_tree ptr h1 == Leaf))

val update_data (#a: Type0) (ptr: t a) (new_v: a)
    : SteelSel unit
      (linked_tree ptr) (fun _ -> linked_tree ptr)
      (requires (fun h0 -> Node? (v_linked_tree ptr h0) /\ not (is_null_t ptr)))
      (ensures (fun h0 _ h1 ->
        Node? (v_linked_tree ptr h0) /\ ( // For AF: do not repeat precondition?
        let Node old_v left right = v_linked_tree ptr h0 in
        v_linked_tree ptr h1 == Node new_v left right
      )))

val intro_tree_left_cons (#a: Type0) (ptr: t a) (left : t a)
    : SteelSel unit
      (vptr ptr `star` linked_tree left)
      (fun _ ->  vptr ptr `star` linked_tree left)
      (requires (fun h0 -> get_left (sel ptr h0) == null_t))
      (ensures (fun h0 _ h1 ->
        get_data (sel ptr h1) == get_data (sel ptr h0) /\
        get_left (sel ptr h1) == left /\
        get_right (sel ptr h1) == get_right (sel ptr h0) /\
        v_linked_tree left h0 == v_linked_tree left h1
      ))


(**** High-level operations on trees *)

val append_tree_left (#a: Type0) (ptr: t a) (left : t a)
    : SteelSel unit
      (linked_tree ptr `star` linked_tree left)
      (fun _ ->  linked_tree ptr)
      (requires (fun h0 -> match v_linked_tree ptr h0 with Node _ Leaf _ -> True | _ -> False))
      (ensures (fun h0 _ h1 ->
        match v_linked_tree ptr h0, v_linked_tree ptr h1 with
        | Node old_data Leaf old_right, Node new_data new_left new_right ->
          old_data == new_data /\
          new_left == v_linked_tree left h0 /\
          new_right == old_right
        | _, _ -> False
      ))

(** Self-balancing part of trees *)
