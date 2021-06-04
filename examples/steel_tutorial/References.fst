module References

open FStar.Ghost
open Steel.FractionalPermission
open Steel.Effect.Atomic
open Steel.Effect
open Steel.Reference

/// Some examples using Steel references with fractional permissions

#push-options "--fuel 0 --ifuel 0 --ide_id_info_off"

(** Swap examples **)

/// The textbook separation logic swap, with the standard pts_to assertion
let swap_textbook (#a:Type0) (r1 r2:ref a) (v1 v2:erased a) : SteelT unit
  (pts_to r1 full_perm v1 `star` pts_to r2 full_perm v2)
  (fun _ -> pts_to r1 full_perm v2 `star` pts_to r2 full_perm v1)
  = let x1 = read_pt r1 in
    let x2 = read_pt r2 in
    write_pt r1 x2;
    write_pt r2 x1;
    // The extra trailing unit is a needed to trigger smt rewriting of x1 into v1 and x2 into v2
    // It might be solved once we have smt_rewrites in subcomp
    ()

/// A selector version of swap, more idiomatic in Steel
let swap_selector (#a:Type0) (r1 r2:ref a) : Steel unit
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
let main_ref () : Steel int emp (fun _ -> emp)
  (requires fun _ -> True)
  (ensures fun _ x _ -> x == 1)
  = // Allocating reference r
    let r = alloc 0 in
    // Writing value 2 in the newly allocated reference
    write r 2;
    // Reading value of r in memory. This was set to 2 just above
    let v = read r in
    // Freeing reference r
    free r;
    // The returned value is equal to 1, the context is now empty
    v - 1

/// Returning a new reference [r'], which is a copy of reference [r]
let copy_ref (#a:Type0) (r:ref a) : Steel (ref a)
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
