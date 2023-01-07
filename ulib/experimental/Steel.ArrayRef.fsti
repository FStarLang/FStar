module Steel.ArrayRef

open Steel.FractionalPermission
open Steel.Memory
open Steel.Effect.Common
open Steel.Effect
open Steel.Effect.Atomic

(** This module provides the same interface as Steel.Reference, however, it builds on top
    of Steel.Array to enable the interoperation between arrays and references.
    Similarly to C, a reference is defined as an array of length 1 *)

/// An abstract datatype for references
inline_for_extraction
val ref ([@@@strictly_positive] a:Type0) : Type0

/// The null pointer
[@@ noextract_to "krml"]
inline_for_extraction
val null (#a:Type0) : ref a

/// Checking whether a pointer is null can be done in a decidable way
[@@ noextract_to "krml"]
inline_for_extraction
val is_null (#a:Type0) (r:ref a) : (b:bool{b <==> r == null})

/// An abstract separation logic predicate stating that reference [r] is valid in memory.

val ptrp (#a:Type0) (r:ref a) ([@@@smt_fallback] p: perm) : slprop u#1

[@@ __steel_reduce__; __reduce__]
unfold
let ptr (#a:Type0) (r:ref a) : slprop u#1 = ptrp r full_perm

/// A selector for references, returning the value of type [a] stored in memory

val ptrp_sel (#a:Type0) (r:ref a) (p: perm) : selector a (ptrp r p)

[@@ __steel_reduce__; __reduce__]
unfold
let ptr_sel (#a:Type0) (r:ref a) : selector a (ptr r) = ptrp_sel r full_perm

/// Combining the separation logic predicate and selector into a vprop
[@@ __steel_reduce__]
let vptr' #a r p : vprop' =
  {hp = ptrp r p;
   t = a;
   sel = ptrp_sel r p}

[@@ __steel_reduce__]
unfold
let vptrp (#a: Type) (r: ref a) ([@@@smt_fallback] p: perm) = VUnit (vptr' r p)

[@@ __steel_reduce__; __reduce__]
unfold
let vptr r = vptrp r full_perm

/// A wrapper to access a reference selector more easily.
/// Ensuring that the corresponding ptr vprop is in the context is done by
/// calling a variant of the framing tactic, as defined in Steel.Effect.Common

[@@ __steel_reduce__]
let selp (#a:Type) (#p:vprop) (r:ref a) (pr: perm)
  (h:rmem p{FStar.Tactics.with_tactic selector_tactic (can_be_split p (vptrp r pr) /\ True)})
  = h (vptrp r pr)

[@@ __steel_reduce__]
let sel (#a:Type) (#p:vprop) (r:ref a)
  (h:rmem p{FStar.Tactics.with_tactic selector_tactic (can_be_split p (vptr r) /\ True)})
  = h (vptr r)

/// Allocates a reference with value [x].
inline_for_extraction
val malloc (#a:Type0) (x:a) : Steel (ref a)
  emp (fun r -> vptr r)
  (requires fun _ -> True)
  (ensures fun _ r h1 -> sel r h1 == x /\ not (is_null r))

/// Frees a reference [r]
inline_for_extraction
val free (#a:Type0) (r:ref a) : Steel unit
  (vptr r) (fun _ -> emp)
  (requires fun _ -> True)
  (ensures fun _ _ _ -> True)

/// Reads the current value of reference [r]
inline_for_extraction
val readp (#a:Type0) (r:ref a) (p: perm) : Steel a
  (vptrp r p) (fun _ -> vptrp r p)
  (requires fun _ -> True)
  (ensures fun h0 x h1 -> h0 (vptrp r p) == h1 (vptrp r p) /\ x == h1 (vptrp r p))

inline_for_extraction
let read (#a:Type0) (r:ref a) : Steel a
  (vptr r) (fun _ -> vptr r)
  (requires fun _ -> True)
  (ensures fun h0 x h1 -> sel r h0 == sel r h1 /\ x == sel r h1)
= readp r full_perm

/// Writes value [x] in reference [r]
inline_for_extraction
val write (#a:Type0) (r:ref a) (x:a) : Steel unit
  (vptr r) (fun _ -> vptr r)
  (requires fun _ -> True)
  (ensures fun _ _ h1 -> x == sel r h1)

val share (#a:Type0) (#uses:_) (#p: perm) (r:ref a)
  : SteelGhost unit uses
    (vptrp r p)
    (fun _ -> vptrp r (half_perm p) `star` vptrp r (half_perm p))
    (fun _ -> True)
    (fun h _ h' ->
      h' (vptrp r (half_perm p)) == h (vptrp r p)
    )

val gather_gen (#a:Type0) (#uses:_) (r:ref a) (p0:perm) (p1:perm)
  : SteelGhost perm uses
    (vptrp r p0 `star` vptrp r p1)
    (fun res -> vptrp r res)
    (fun _ -> True)
    (fun h res h' ->
      res == sum_perm p0 p1 /\
      h' (vptrp r res) == h (vptrp r p0) /\
      h' (vptrp r res) == h (vptrp r p1)
    )

val gather (#a: Type0) (#uses: _) (#p: perm) (r: ref a)
  : SteelGhost unit uses
      (vptrp r (half_perm p) `star` vptrp r (half_perm p))
      (fun _ -> vptrp r p)
      (fun _ -> True)
      (fun h _ h' ->
        h' (vptrp r p) == h (vptrp r (half_perm p))
      )

/// A stateful lemma variant of the pts_to_not_null lemma above.
/// This stateful function is computationally irrelevant and does not modify memory
val vptrp_not_null (#opened: _)
  (#a: Type)
  (r: ref a)
  (p: perm)
: SteelGhost unit opened
    (vptrp r p)
    (fun _ -> vptrp r p)
    (fun _ -> True)
    (fun h0 _ h1 ->
      h0 (vptrp r p) == h1 (vptrp r p) /\
      is_null r == false
    )

let vptr_not_null (#opened: _)
  (#a: Type)
  (r: ref a)
: SteelGhost unit opened
    (vptr r)
    (fun _ -> vptr r)
    (fun _ -> True)
    (fun h0 _ h1 ->
      sel r h0 == sel r h1 /\
      is_null r == false
    )
= vptrp_not_null r full_perm
