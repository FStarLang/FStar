module CQueue.Cell
open Steel.Memory
open Steel.Effect
open Steel.Effect.Atomic
open Steel.FractionalPermission
open Steel.Reference

(* A C lvalue view of a cell struct, as a pair of two references for its data and next fields *)

val ccell_ptrvalue (a: Type0) : Tot Type0 (* "ccell *" seen as a rvalue *)

val ccell_ptrvalue_null (a: Type0) : Tot (ccell_ptrvalue a)

(* Pointer arithmetic: comparison to null, and pointer to fields. TODO: split these operations between Ghost and Steel, with a proper model of a "permission to do pointer arithmetic without actually reading the value/dereferencing" *)

val ccell_ptrvalue_is_null (#a: Type0) (c: ccell_ptrvalue a) : Pure bool
  (requires True)
  (ensures (fun b -> b == true <==> c == ccell_ptrvalue_null a))

let ccell_lvalue (a: Type0) = (c: ccell_ptrvalue a { ccell_ptrvalue_is_null c == false }) (* "ccell" seen as a lvalue, or "ccell * const". IMPORTANT: one MUST NOT use "ref ccell_lvalue" in C code. In other words, ref can be used to model pointers to rvalues only. *)

val ccell_data (#a: Type0) (c: ccell_lvalue a) : Pure (ref a)
  (requires True)
  (ensures (fun v -> ~ (is_null v)))

val ccell_next (#a: Type0) (c: ccell_lvalue a) : Pure (ref (ccell_ptrvalue a))
  (requires True)
  (ensures (fun v -> ~ (is_null v)))

(* Important: we DO NOT provide a pure constructor for this data type, since its fields MUST be allocated at the same time and a cell MUST NOT be forged from references that would not come from such same-time allocation. *)

(* The high-level value of a cell (should NEVER be used in C code, only in specs) *)

noeq
type vcell (a: Type0) = {
  vcell_data : a;
  vcell_next : ccell_ptrvalue a;
}

val ccell_hp
  (#a: Type0)
  (c: ccell_ptrvalue a)
: Tot (slprop u#1)

val ccell_sel
  (#a: Type0)
  (c: ccell_ptrvalue a)
: GTot (selector (vcell a) (ccell_hp c))

[@__steel_reduce__]
let ccell'
  (#a: Type0)
  (c: ccell_ptrvalue a)
: GTot vprop'
= {
  hp = ccell_hp c;
  t = vcell a;
  sel = ccell_sel c;
}

[@__steel_reduce__]
let ccell (#a: Type0) (c: ccell_ptrvalue a) : Tot vprop =
  VUnit (ccell' c)

val intro_ccell
  (#opened: _)
  (#a: Type0)
  (c: ccell_lvalue a)
: SteelGhost unit opened
    (vptr (ccell_data c) `star` vptr (ccell_next c))
    (fun _ -> ccell c)
    (fun _ -> True)
    (fun h res h' ->
      h' (ccell c) == ({ vcell_data = h (vptr (ccell_data c)); vcell_next = h (vptr (ccell_next c))})
    )

// TODO: ccell_data and ccell_next should not be freeable
val elim_ccell_ghost
  (#opened: _)
  (#a: Type0)
  (c: ccell_ptrvalue a)
: SteelGhost (Ghost.erased (ccell_lvalue a)) opened
    (ccell c)
    (fun c' -> vptr (ccell_data c') `star` vptr (ccell_next c'))
    (fun _ -> True)
    (fun h c' h' ->
      ccell_ptrvalue_is_null c == false /\
      (c' <: ccell_ptrvalue a) == c /\
      h (ccell c) == { vcell_data = h' (vptr (ccell_data c')); vcell_next = h' (vptr (ccell_next c')) }
    )

val elim_ccell
  (#opened: _)
  (#a: Type0)
  (c: ccell_ptrvalue a)
: SteelAtomic (ccell_lvalue a) opened
    (ccell c)
    (fun c' -> vptr (ccell_data c') `star` vptr (ccell_next c'))
    (fun _ -> True)
    (fun h c' h' ->
      ccell_ptrvalue_is_null c == false /\
      (c' <: ccell_ptrvalue a) == c /\
      h (ccell c) == { vcell_data = h' (vptr (ccell_data c')); vcell_next = h' (vptr (ccell_next c')) }
    )

val ccell_not_null
  (#opened: _)
  (#a: Type0)
  (c: ccell_ptrvalue a)
: SteelGhost (squash (ccell_ptrvalue_is_null c == false)) opened
    (ccell c)
    (fun _ -> ccell c)
    (fun _ -> True)
    (fun h _ h' ->
      h' (ccell c) == h (ccell c)
    )

val freeable (#a: Type0) (c: ccell_ptrvalue a) : Tot prop

val alloc_cell
  (#a: Type0)
  (data: a)
  (next: ccell_ptrvalue a)
: Steel (ccell_lvalue a)
    emp
    (fun res -> ccell res)
    (requires (fun _ -> True))
    (ensures (fun _ res h' ->
      h' (ccell res) == ({ vcell_data = data; vcell_next = next; }) /\
      freeable res
    ))

val free_cell
  (#a: Type0)
  (c: ccell_ptrvalue a) // could be ccell_lvalue, but ccell gives the right refinement
: Steel unit
    (ccell c)
    (fun _ -> emp)
    (fun _ -> freeable c)
    (fun _ _ _ -> True)
