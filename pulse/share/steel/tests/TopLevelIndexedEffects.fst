module TopLevelIndexedEffects

//
// However sometimes we may want to constrain the effect arguments
//   when the effect appears at the top-level
//
// See e.g. Steel.ST.Effect.STBase that constrains the preconditions at the top-level
//

#push-options "--compat_pre_typed_indexed_effects"

open Steel.FractionalPermission
open Steel.ST.Effect
open Steel.ST.SpinLock
open Steel.ST.Util
open Steel.ST.Reference

let t : (r:ref int & lock (pts_to r full_perm 2))  =
  (let r = alloc #int 2 in
   let l = new_lock (pts_to r full_perm 2) in
   return (| r, l |)) <: STT _ emp (fun _ -> emp)

assume val r : ref int

//
// This fails with smt error since the top-level effect requires
//   pre assertion to be emp, and here it is (pts_to ...)
// F* tries to prove they are equal using SMT (and fails)
//

[@@ expect_failure]
let t0 : unit =
  write #int #(Ghost.hide 0) r 1
    <: STT unit
           (pts_to r full_perm (Ghost.hide 0)) (fun _ -> pts_to r full_perm (Ghost.hide 1))
#pop-options
