(*
   Copyright 2021 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)

module Steel.ST.Reference
open FStar.Ghost
open Steel.ST.Util

module U32 = FStar.UInt32

(** This module provides a reference whose ownership is controlled
    using fractional permissions.
    
    It provides a distinguished null reference too, which is
    extractable to C as a null pointer. *)

/// The main ref type.
///
/// It's in universe zero, so refs can be stored in the heap, you can
/// have [ref (ref a)] etc.
val ref (a:Type0)
  : Type0

/// The null reference
val null (#a:Type0) 
  : ref a

/// Nullness is decidable with a pure function
val is_null (#a:Type0) (r:ref a)
  : b:bool{b <==> r == null}

/// The main representation predicate
///
/// Both the permissions [p] and the value [v] are marked with the
/// [smt_fallback] attribute. This allows the Steel unifier to produce
/// equality goals discharged by SMT to relate instances of the
/// [pts_to] predicate that differ on the [p] and [v] arguments.
///
/// For instance, [pts_to r (sum_perm (half_perm p) (half_perm p)) (v + 1)]
/// is unifiable with [pts_to r p (1 + v)]
val pts_to (#a:Type0)
           (r:ref a)
           ([@@@smt_fallback] p:perm)
           ([@@@smt_fallback] v:a)
  : vprop

/// A reference can point to at most one value
val pts_to_injective_eq (#a: Type)
                        (#opened:inames)
                        (#p0 #p1:perm)
                        (#v0 #v1: a)
                        (r: ref a)
  : STGhost unit opened
      (pts_to r p0 v0 `star` pts_to r p1 v1)
      (fun _ -> pts_to r p0 v0 `star` pts_to r p1 v0)
      (requires True)
      (ensures fun _ -> v0 == v1)

/// Null references can't point to anything
val pts_to_not_null (#a:Type)
                    (#opened:inames)
                    (#p:perm)
                    (#v:a)
                    (r:ref a)
  : STGhost unit opened
      (pts_to r p v)
      (fun _ -> pts_to r p v)
      (requires True)
      (ensures fun _ -> r =!= null)
                    
/// Allocating a reference returns full-permission to a non-null
/// reference pointing to the initializer [x].
///
/// We do not model memory exhaustion
val alloc (#a:Type) (x:a)
  : ST (ref a)
      emp 
      (fun r -> pts_to r full_perm x)
      (requires True)
      (ensures fun r -> not (is_null r))

/// Reads the value in reference [r]. The postcondition ensures that
/// the returned value is equal to the index [v].
val read (#a:Type)
         (#p:perm)
         (#v:erased a)
         (r:ref a)
  : ST a
      (pts_to r p v)
      (fun x -> pts_to r p v)
      (requires True)
      (ensures fun x -> x == Ghost.reveal v)

/// Writes value `x` in the reference `r`, as long as we have full
/// ownership of `r`
val write (#a:Type0)
          (#v:erased a)
          (r:ref a)
          (x:a)
  : STT unit
      (pts_to r full_perm v)
      (fun _ -> pts_to r full_perm x)

/// Frees reference [r], as long as we have full ownership of [r]
val free (#a:Type0)
         (#v:erased a)
         (r:ref a)
  : STT unit
    (pts_to r full_perm v) (fun _ -> emp)

/// Splits the permission on reference [r] into two. This function is
/// computationally irrelevant (it has effect SteelGhost)
val share (#a:Type0)
          (#uses:_)
          (#p:perm)
          (#v:erased a)
          (r:ref a)
  : STGhostT unit uses
      (pts_to r p v)
      (fun _ -> pts_to r (half_perm p) v `star` pts_to r (half_perm p) v)

/// Combines permissions on reference [r]. This function is
/// computationally irrelevant (it has effect SteelGhost)
val gather (#a:Type0)
           (#uses:_) 
           (#p0 p1:perm)
           (#v0 #v1:erased a)
           (r:ref a)
  : STGhost unit uses
      (pts_to r p0 v0 `star` pts_to r p1 v1)
      (fun _ -> pts_to r (sum_perm p0 p1) v0)
      (requires True)
      (ensures fun _ -> v0 == v1)

/// Atomic operations (read, write, and cas) on references,
///   restricted to small types
///
/// Currently we are exporting only for U32,
///   other types can be similarly added

val atomic_read_u32 (#opened:_)
  (#p:perm)
  (#v:erased U32.t)
  (r:ref U32.t)
  : STAtomic U32.t opened
      (pts_to r p v)
      (fun x -> pts_to r p v)
      (requires True)
      (ensures fun x -> x == Ghost.reveal v)

val atomic_write_u32 (#opened:_)
  (#v:erased U32.t)
  (r:ref U32.t)
  (x:U32.t)
  : STAtomicT unit opened
      (pts_to r full_perm v)
      (fun _ -> pts_to r full_perm x)

val cas_u32 (#uses:inames)
        (v:Ghost.erased U32.t)
        (r:ref U32.t)
        (v_old v_new:U32.t)
  : STAtomicT (b:bool{b <==> (Ghost.reveal v == v_old)})
      uses
      (pts_to r full_perm v)
      (fun b -> if b then pts_to r full_perm v_new else pts_to r full_perm v)

// A reinterpretation of pts_to with selectors

module C = Steel.ST.Combinators

val ptrp (#a:Type0) (r:ref a) ([@@@smt_fallback] p: perm) : slprop u#1
val ptrp_sel (#a:Type0) (r:ref a) (p: perm) : selector a (ptrp r p)

[@@ __steel_reduce__]
let vptr' #a r p : vprop' =
  {hp = ptrp r p;
   t = a;
   sel = ptrp_sel r p}

[@@ __steel_reduce__]
unfold
let vptrp (#a: Type) (r: ref a) ([@@@smt_fallback] p: perm) = VUnit (vptr' r p)

val vptrp_intro
  (#inames: _)
  (#a: Type) (r: ref a) (p: perm) (v: a)
: STGhostT unit inames
    (pts_to r p v)
    (fun _ -> vptrp r p `vrefine` C.equals v)

val vptrp_elim
  (#inames: _)
  (#a: Type) (r: ref a) (p: perm) (v: a)
: STGhostT unit inames
    (vptrp r p `vrefine` C.equals v)
    (fun _ -> pts_to r p v)
