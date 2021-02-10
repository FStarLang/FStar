module Selectors.BST

open Steel.Memory
open Steel.SelEffect

module Spec = FStar.Trees

(*** Type declarations *)

(**** Base types *)

(** A node of the tree *)
val node (a b: Type0) {| Spec.ordered a |}  : Type

(** A tree is a ref to a node, themselves referencing other nodes *)
let t (a b: Type0) {| Spec.ordered a |} = ref (node a b)

(** This type reflects the contents of a tree without the memory layout *)
type tree (a b: Type0) {| Spec.ordered a |} = Spec.bst a b

(**** Slprop and selector *)

(** The separation logic proposition representing the memory layout of the tree *)
val tree_sl (#a #b: Type0) {| Spec.ordered a |} (r: t a b) : slprop u#1

(** Selector retrieving the contents of a tree in memory *)
val tree_sel (#a #b: Type0) {| Spec.ordered a |} (r: t a b) : selector (tree a b) (tree_sl r)

[@@__steel_reduce__]
let linked_tree' (#a #b: Type0) {| Spec.ordered a |} (r: t a b) : vprop' = {
  hp = tree_sl r;
  t = tree a b;
  sel = tree_sel r
}

(** The view proposition encapsulating the separation logic proposition and the selector *)
unfold let linked_tree (#a #b: Type0) {| Spec.ordered a |} (tr: t a b) : vprop =
  VUnit (linked_tree' tr)

(** This convenience helper retrieves the contents of a tree from an [rmem] *)
[@@ __steel_reduce__]
let v_linked_tree
  (#a #b:Type0)
  {| Spec.ordered a |}
  (#p:vprop)
  (r:t a b)
  (h:rmem p{
    FStar.Tactics.with_tactic selector_tactic (can_be_split p (linked_tree r) /\ True)
  })
    : GTot (tree a b)
  = h (linked_tree r)

(*** Operations *)

(**** Operations on nodes *)

val get_left (#a #b: Type0) {| Spec.ordered a |} (n: node a b) : t a b
val get_right (#a #b: Type0) {| Spec.ordered a |} (n: node a b) : t a b
val get_data (#a #b: Type0) {| Spec.ordered a |} (n: node a b) : b
val get_key (#a #b: Type0) {| Spec.ordered a |} (n: node a b) : a

val mk_node  (#a #b: Type0) {| Spec.ordered a |} (left right: t a b) (k: a) (v: b)
    : Pure (node a b)
      (requires True)
      (ensures (fun n ->
        get_left n == left /\
        get_right n == right /\
        get_data n == v))

(**** Low-level operations on trees *)

val null_t (#a #b: Type0) {| Spec.ordered a |} : t a b
val is_null_t (#a #b: Type0) {| Spec.ordered a |} (r: t a b) : (b:bool{b <==> r == null_t})

val intro_linked_tree_leaf (#a #b: Type0) {| Spec.ordered a |} (_: unit)
    : SteelSel unit
      vemp (fun _ -> linked_tree (null_t #a #b))
      (requires (fun _ -> True))
      (ensures (fun _ _ h1 -> v_linked_tree #a #b (null_t #a #b) h1 == Spec.Leaf))

val elim_linked_tree_leaf (#a #b: Type0) {| Spec.ordered a |} (ptr: t a b)
    : SteelSel unit
       (linked_tree ptr) (fun _ -> linked_tree ptr)
       (requires (fun _ -> is_null_t ptr))
       (ensures (fun h0 _ h1 ->
         v_linked_tree ptr h0 == v_linked_tree ptr h1 /\
         v_linked_tree ptr h1 == Spec.Leaf))

val pack_tree (#a #b: Type0) {| Spec.ordered a |} (ptr: t a b) (left: t a b) (right: t a b)
    : SteelSel unit
      (vptr ptr `star` linked_tree left `star` linked_tree right)
      (fun _ -> linked_tree ptr)
      (requires (fun h0 ->
        not (is_null_t ptr) /\
        get_left (sel ptr h0) == left /\
        get_right (sel ptr h0) == right /\
        Spec.forall_keys (v_linked_tree left h0) (Spec.key_left (get_key (sel ptr h0))) /\
        Spec.forall_keys (v_linked_tree right h0) (Spec.key_right (get_key (sel ptr h0)))
      ))
      (ensures (fun h0 _ h1 ->
        v_linked_tree ptr h1 ==
          Spec.Node
            ({ Spec.key = get_key (sel ptr h0); Spec.payload = get_data (sel ptr h0)})
            (v_linked_tree left h0) (v_linked_tree right h0)
      ))

val unpack_tree (#a #b: Type0) {| Spec.ordered a |} (ptr: t a b)
    : SteelSel (t a b & t a b)
      (linked_tree ptr)
      (fun (left, right) ->
        linked_tree left `star` linked_tree right `star` vptr ptr)
      (requires (fun h0 -> not (is_null_t ptr)))
      (ensures (fun h0 (left, right) h1 ->
        v_linked_tree ptr h0 == Spec.Node
          (admit()) // AF: why can't we put get_data (sel h1 ptr)
          (v_linked_tree left h1)
          (v_linked_tree right h1)
      ))

(**** High-level operations on trees *)

val insert (#a #b: Type0) {| Spec.ordered a |} (ptr: t a b) (k : a) (v: b)
    : SteelSel unit
      (linked_tree ptr)
      (fun _ ->  linked_tree ptr)
      (requires (fun h0 -> True))
      (ensures (fun h0 _ h1 -> v_linked_tree ptr h1 == Spec.insert_bst (v_linked_tree ptr h0) k v))
