module CQueue.LList
include CQueue.Cell
open Steel.Memory
open Steel.Effect.Atomic
open Steel.Effect
open Steel.FractionalPermission
open Steel.Reference

(* A C lvalue view of a llist struct, as a pair of two references for its head and tail fields  (C language aspects only, no semantic content)

   See CQueue.c: cllist_*
*)

val cllist_ptrvalue (a: Type0) : Tot Type0 (* "cllist *" seen as a rvalue *)

val cllist_ptrvalue_null (a: Type0) : Tot (cllist_ptrvalue a)

(* Pointer arithmetic: comparison to null, and pointer to fields. TODO: split these operations between Ghost and Steel, with a proper model of a "permission to do pointer arithmetic without actually reading the value/dereferencing" *)

val cllist_ptrvalue_is_null (#a: Type0) (c: cllist_ptrvalue a) : Pure bool
  (requires True)
  (ensures (fun b -> b == true <==> c == cllist_ptrvalue_null a))

let cllist_lvalue (a: Type0) = (c: cllist_ptrvalue a { cllist_ptrvalue_is_null c == false }) (* "cllist" seen as a lvalue, or "cllist * const". IMPORTANT: one MUST NOT use "ref cllist_lvalue" in C code. In other words, ref can be used to model pointers to rvalues only. *)

val cllist_head (#a: Type0) (c: cllist_lvalue a) : Pure (ref (ccell_ptrvalue a))
  (requires True)
  (ensures (fun v -> ~ (is_null v)))

val cllist_tail (#a: Type0) (c: cllist_lvalue a) : Pure (ref (ref (ccell_ptrvalue a)))
  (requires True)
  (ensures (fun v -> ~ (is_null v)))

(* Important: we DO NOT provide a pure constructor for this data type, since its fields MUST be allocated at the same time and a cell MUST NOT be forged from references that would not come from such same-time allocation. *)

(* The "high-level" value of a llist (should NEVER be used in C code, only in specs) *)

noeq
type vllist (a: Type0) = {
  vllist_head : ccell_ptrvalue a;
  vllist_tail : ref (ccell_ptrvalue a);
}

val cllist_hp
  (#a: Type0)
  (c: cllist_ptrvalue a)
: Tot (slprop u#1)

val cllist_sel
  (#a: Type0)
  (c: cllist_ptrvalue a)
: GTot (selector (vllist a) (cllist_hp c))

[@__steel_reduce__]
let cllist'
  (#a: Type0)
  (c: cllist_ptrvalue a)
: GTot vprop'
= {
  hp = cllist_hp c;
  t = vllist a;
  sel = cllist_sel c;
}

[@__steel_reduce__]
let cllist (#a: Type0) (c: cllist_ptrvalue a) : Tot vprop =
  VUnit (cllist' c)

val intro_cllist
  (#opened: _)
  (#a: Type0)
  (c: cllist_lvalue a)
: SteelGhost unit opened
    (vptr (cllist_head c) `star` vptr (cllist_tail c))
    (fun _ -> cllist c)
    (fun _ -> True)
    (fun h res h' ->
      h' (cllist c) == ({ vllist_head = h (vptr (cllist_head c)); vllist_tail = h (vptr (cllist_tail c))})
    )

// TODO: cllist_head and cllist_tail should not be freeable
val elim_cllist_ghost
  (#opened: _)
  (#a: Type0)
  (c: cllist_ptrvalue a)
: SteelGhost (Ghost.erased (cllist_lvalue a)) opened
    (cllist c)
    (fun c' -> vptr (cllist_head c') `star` vptr (cllist_tail c'))
    (fun _ -> True)
    (fun h c' h' ->
      cllist_ptrvalue_is_null c == false /\
      (c' <: cllist_ptrvalue a) == c /\
      h (cllist c) == { vllist_head = h' (vptr (cllist_head c')); vllist_tail = h' (vptr (cllist_tail c')) }
    )

val elim_cllist
  (#opened: _)
  (#a: Type0)
  (c: cllist_ptrvalue a)
: SteelAtomic (cllist_lvalue a) opened
    (cllist c)
    (fun c' -> vptr (cllist_head c') `star` vptr (cllist_tail c'))
    (fun _ -> True)
    (fun h c' h' ->
      cllist_ptrvalue_is_null c == false /\
      (c' <: cllist_ptrvalue a) == c /\
      h (cllist c) == { vllist_head = h' (vptr (cllist_head c')); vllist_tail = h' (vptr (cllist_tail c')) }
    )

val cllist_not_null
  (#opened: _)
  (#a: Type0)
  (c: cllist_ptrvalue a)
: SteelGhost (squash (cllist_ptrvalue_is_null c == false)) opened
    (cllist c)
    (fun _ -> cllist c)
    (fun _ -> True)
    (fun h _ h' ->
      h' (cllist c) == h (cllist c)
    )

val freeable (#a: Type0) (c: cllist_ptrvalue a) : Tot prop

val alloc_llist
  (#a: Type0)
  (head: ccell_ptrvalue a)
  (tail: ref (ccell_ptrvalue a))
: Steel (cllist_lvalue a)
    emp
    (fun res -> cllist res)
    (requires (fun _ -> True))
    (ensures (fun _ res h' ->
      h' (cllist res) == ({ vllist_head = head; vllist_tail = tail; }) /\
      freeable res
    ))

val free_llist
  (#a: Type0)
  (c: cllist_ptrvalue a) // could be cllist_lvalue, but cllist gives the right refinement
: Steel unit
    (cllist c)
    (fun _ -> emp)
    (fun _ -> freeable c)
    (fun _ _ _ -> True)
