module Selectors.Tree

open Selectors.Tree.Core
open Steel.Memory
open Steel.Effect.Atomic
open Steel.Effect

module Spec = Trees

#set-options "--ide_id_info_off"

(**** High-level operations on trees *)

val append_left (#a: Type0) (ptr: t a) (v: a)
    : Steel (t a)
      (linked_tree ptr)
      (fun ptr' ->  linked_tree ptr')
      (requires (fun h0 -> True))
      (ensures (fun h0 ptr' h1 -> v_linked_tree ptr' h1 == Spec.append_left (v_linked_tree ptr h0) v))

val append_right (#a: Type0) (ptr: t a) (v: a)
    : Steel (t a)
      (linked_tree ptr)
      (fun ptr' ->  linked_tree ptr')
      (requires (fun h0 -> True))
      (ensures (fun h0 ptr' h1 ->
        v_linked_tree ptr' h1 == Spec.append_right (v_linked_tree ptr h0) v
      ))

val height (#a: Type0) (ptr: t a)
    : Steel nat (linked_tree ptr) (fun _ -> linked_tree ptr)
    (requires fun _ -> True)
    (ensures fun h0 x h1 ->
        v_linked_tree ptr h0 == v_linked_tree ptr h1 /\
        Spec.height (v_linked_tree ptr h0) == x)

val member (#a: eqtype) (ptr: t a) (v: a)
    : Steel bool (linked_tree ptr) (fun _ -> linked_tree ptr)
    (requires fun _ -> True)
    (ensures fun h0 b h1 ->
        v_linked_tree ptr h0 == v_linked_tree ptr h1 /\
        (Spec.mem (v_linked_tree ptr h0) v <==> b))

val rotate_left (#a: Type) (ptr: t a)
    : Steel (t a) (linked_tree ptr) (fun ptr' -> linked_tree ptr')
    (requires fun h0 -> Some? (Spec.rotate_left (v_linked_tree ptr h0)))
    (ensures (fun h0 ptr' h1 ->
        Spec.rotate_left (v_linked_tree ptr h0) == Some (v_linked_tree ptr' h1)
    ))

val rotate_right (#a: Type) (ptr: t a)
    : Steel (t a) (linked_tree ptr) (fun ptr' -> linked_tree ptr')
    (requires fun h0 -> Some? (Spec.rotate_right (v_linked_tree ptr h0)))
    (ensures (fun h0 ptr' h1 ->
        Spec.rotate_right (v_linked_tree ptr h0) == Some (v_linked_tree ptr' h1)
    ))

val rotate_right_left (#a: Type) (ptr: t a)
    : Steel (t a) (linked_tree ptr) (fun ptr' -> linked_tree ptr')
    (requires fun h0 -> Some? (Spec.rotate_right_left (v_linked_tree ptr h0)))
    (ensures (fun h0 ptr' h1 ->
        Spec.rotate_right_left (v_linked_tree ptr h0) == Some (v_linked_tree ptr' h1)
    ))

val rotate_left_right (#a: Type) (ptr: t a)
    : Steel (t a) (linked_tree ptr) (fun ptr' -> linked_tree ptr')
    (requires fun h0 -> Some? (Spec.rotate_left_right (v_linked_tree ptr h0)))
    (ensures (fun h0 ptr' h1 ->
        Spec.rotate_left_right (v_linked_tree ptr h0) == Some (v_linked_tree ptr' h1)
    ))

val is_balanced (#a: Type) (ptr: t a)
    : Steel bool (linked_tree ptr) (fun _ -> linked_tree ptr)
    (requires fun h0 -> True)
    (ensures (fun h0 b h1 ->
        v_linked_tree ptr h0 == v_linked_tree ptr h1 /\
        Spec.is_balanced (v_linked_tree ptr h0) == b))

val rebalance_avl (#a: Type) (cmp:Spec.cmp a) (ptr: t a)
    : Steel (t a) (linked_tree ptr) (fun ptr' -> linked_tree ptr')
    (requires fun h0 -> True)
    (ensures fun h0 ptr' h1 ->
        Spec.rebalance_avl (v_linked_tree ptr h0) == v_linked_tree ptr' h1)

val insert_avl (#a: Type) (cmp:Spec.cmp a) (ptr: t a) (v: a)
    : Steel (t a) (linked_tree ptr) (fun ptr' -> linked_tree ptr')
    (requires fun h0 -> Spec.is_avl cmp (v_linked_tree ptr h0))
    (ensures fun h0 ptr' h1 ->
        Spec.insert_avl cmp (v_linked_tree ptr h0) v == v_linked_tree ptr' h1)
