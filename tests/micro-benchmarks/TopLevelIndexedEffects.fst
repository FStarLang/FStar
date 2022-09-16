module TopLevelIndexedEffects

/// See the definition of top_level_effect in FStar.Pervasives.fsti

//
// Defining an identity effect
//

type repr (a:Type) = a
let return (a:Type) (x:a) : repr a = x
let bind (a b:Type) (f:repr a) (g:a -> repr b) : repr b = g f

effect { M (a:Type) with {repr; return; bind}}

let lift_PURE_M (a:Type) (wp:pure_wp a) (f:eqtype_as_type unit -> PURE a wp)
  : Pure (repr a)
         (requires wp (fun _ -> True))
         (ensures fun _ -> True)
  = FStar.Monotonic.Pure.elim_pure_wp_monotonicity wp;
    f ()

sub_effect PURE ~> M = lift_PURE_M

assume val f (_:unit) : M int


//
// If we try to use this effect at the top-level, F* complains
//

[@@ expect_failure]
let n : int = f ()

//
// We define an identical effect N,
//   but with a top-level effect attribute
//

[@@ top_level_effect]
effect { N (a:Type) with {repr; return; bind}}

sub_effect PURE ~> N = lift_PURE_M

//
// And now F* lets the effect go through at the top-level
//

assume val g (_:unit) : N int

let n : int = g ()


//
// However sometimes we may want to constrain the effect arguments
//   when the effect appears at the top-level
//
// See e.g. Steel.ST.Effect.STBase that constrains the preconditions at the top-level
//

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
