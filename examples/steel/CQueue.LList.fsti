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

let cllist_rewrite
  (#a: Type0)
  (c: cllist_lvalue a)
  (x: (ccell_ptrvalue a & ref (ccell_ptrvalue a)))
: GTot (vllist a)
= {
  vllist_head = fst x;
  vllist_tail = snd x;
}

[@@ __steel_reduce__ ; __reduce__] // to avoid manual unfoldings through change_slprop
let cllist_full (#a: Type0) (c: cllist_lvalue a) : Tot vprop =
  (vptr (cllist_head c) `star` vptr (cllist_tail c)) `vrewrite` cllist_rewrite c

[@__reduce__] // to avoid manual unfoldings through change_slprop
let cllist (#a: Type0) (c: cllist_lvalue a) (p: perm) (v: Ghost.erased (vllist a)) : Tot vprop =
  pts_to (cllist_head c) p v.vllist_head `star` pts_to (cllist_tail c) p v.vllist_tail

val cllist_full_cllist
  (#opened: _)
  (#a: Type0)
  (c: cllist_lvalue a)
: SteelGhost (Ghost.erased (vllist a)) opened
    (cllist_full c)
    (fun v -> cllist c full_perm v)
    (fun _ -> True)
    (fun h v _ -> Ghost.reveal v == h (cllist_full c))

val alloc_cllist_full
  (#a: Type0)
  (head: ccell_ptrvalue a)
  (tail: ref (ccell_ptrvalue a))
: Steel (cllist_lvalue a)
    emp
    (fun res -> cllist_full res)
    (requires (fun _ -> True))
    (ensures (fun _ res h' -> h' (cllist_full res) == ({ vllist_head = head; vllist_tail = tail; })))

val alloc_cllist
  (#a: Type0)
  (head: ccell_ptrvalue a)
  (tail: ref (ccell_ptrvalue a))
: Steel (cllist_lvalue a & Ghost.erased (vllist a))
    emp
    (fun res -> cllist (fst res) full_perm (snd res))
    (requires (fun _ -> True))
    (ensures (fun _ res _ -> Ghost.reveal (snd res) == ({ vllist_head = head; vllist_tail = tail })))
