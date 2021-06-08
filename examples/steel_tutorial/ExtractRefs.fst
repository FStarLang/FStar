module ExtractRefs

open FStar.Ghost
open Steel.FractionalPermission
open Steel.Effect.Atomic
open Steel.Effect
open Steel.Reference
module U32 = FStar.UInt32

/// Some examples using Steel references with fractional permissions

#push-options "--fuel 0 --ifuel 0 --ide_id_info_off"

(** Swap examples **)

/// A selector version of swap, more idiomatic in Steel
let swap (r1 r2:ref U32.t) : Steel unit
  (vptr r1 `star` vptr r2)
  (fun _ -> vptr r1 `star` vptr r2)
  (requires fun _ -> True)
  (ensures fun h0 _ h1 ->
    sel r1 h0 == sel r2 h1 /\
    sel r2 h0 == sel r1 h1)
  = let x1 = read r1 in
    let x2 = read r2 in
    write r2 x1;
    write r1 x2

(** Allocating and Freeing references *)

/// Demonstrating standard reference operations
let main_ref () : Steel U32.t emp (fun _ -> emp)
  (requires fun _ -> True)
  (ensures fun _ x _ -> x == 2ul)
  = // Allocating reference r
    let r = alloc 0ul in
    // Writing value 2 in the newly allocated reference
    write r 2ul;
    // Reading value of r in memory. This was set to 2 just above
    let v = read r in
    // Freeing reference r
    free r;
    // The returned value is equal to 1, the context is now empty
    v

/// Returning a new reference [r'], which is a copy of reference [r]
let copy_ref (r:ref U32.t) : Steel (ref U32.t)
  (vptr r)
  // We allocated a new reference r', which is the return value
  (fun r' -> vptr r `star` vptr r')
  (requires fun _ -> True)
  (ensures fun h0 r' h1 ->
    // reference r was not modified
    sel r h0 == sel r h1 /\
    // After copying, reference r' contains the same value as reference r
    sel r' h1 == sel r h1)

  = let x = read r in
    let r' = alloc x in
    r'

(* Sharing and gathering references *)

// AF: TODO after merging Tahina's request to provide gather/share for selector references

// Example1: Sharing a reference r. Executing a function f operating on half_perm of r.
// Gathering, and getting for free that r was unchanged
