module LListQueue.Cell
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

(* FIXME:
   1/ revise the permission system for individual references to forbid freeing just one field,
      but without assuming that such references are "non-freeable forever."
   2/ add a "cell-level freeable" permission to free the whole cell *)

[@__reduce__] // to avoid manual unfoldings through change_slprop 
let ccell (#a: Type0) (c: ccell_lvalue a) (p: perm) (v: Ghost.erased (vcell a)) : Tot slprop =
  pts_to (ccell_data c) p v.vcell_data `star` pts_to (ccell_next c) p v.vcell_next

let ccellp (#a: Type0) (c: ccell_ptrvalue a) (p: perm) (v: Ghost.erased (option (vcell a))) : Tot slprop =
  match ccell_ptrvalue_is_null c, Ghost.reveal v with
  | false, Some v ->
    let c : ccell_lvalue a = c in
    ccell c p (Ghost.hide v)
  | true, None -> emp
  | _ -> pure False

let ccellp_null_intro (#a: Type0) (c: ccell_ptrvalue a) (p: perm) : Steel unit
  emp
  (fun _ -> ccellp c p None)
  (requires (fun _ -> ccell_ptrvalue_is_null c == true))
  (ensures (fun _ _ _ -> True))
= 
  change_slprop emp (ccellp c p None) (fun _ -> ())

let ccellp_is_null
  (#a: Type0) (c: ccell_ptrvalue a) (p: perm) (v: Ghost.erased (option (vcell a)))
: Steel unit
    (ccellp c p v)
    (fun _ -> ccellp c p v)
    (requires (fun _ -> True))
    (ensures (fun _ _ _ -> ccell_ptrvalue_is_null c == None? (Ghost.reveal v)))
=
  change_slprop
    (ccellp c p v)
    (ccellp c p v `star` pure (ccell_ptrvalue_is_null c == None? (Ghost.reveal v)))
    (fun m ->
      pure_star_interp (ccellp c p v) (ccell_ptrvalue_is_null c == None? (Ghost.reveal v)) m;
      emp_unit (ccellp c p v);
      match ccell_ptrvalue_is_null c, Ghost.reveal v with
      | false, Some _
      | true, None
        -> ()
      | _ -> pure_interp False m
    );
  elim_pure (ccell_ptrvalue_is_null c == None? (Ghost.reveal v))

val alloc_cell
  (#a: Type0)
  (data: a)
  (next: ccell_ptrvalue a)
: Steel (ccell_lvalue a & Ghost.erased (vcell a))
    emp
    (fun res -> ccell (fst res) full_perm (snd res))
    (requires (fun _ -> True))
    (ensures (fun _ res _ -> Ghost.reveal (snd res) == ({ vcell_data = data; vcell_next = next; })))

val free_cell
  (#a: Type0)
  (c: ccell_lvalue a)
  (v: Ghost.erased (vcell a))
: SteelT unit
    (ccell c full_perm v)
    (fun _ -> emp)
