(*
   Copyright 2020 Microsoft Research

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

val ref (a:Type0)
  : Type0

val null (#a:Type0) 
  : ref a

val is_null (#a:Type0) (r:ref a)
  : b:bool{b <==> r == null}

val pts_to (#a:Type0)
           (r:ref a)
           (p:perm)
           ([@@@smt_fallback] v:a)
  : vprop

val pts_to_injective_eq
      (#a: Type)
      (#opened:inames)
      (#p0 #p1:perm)
      (#v0 #v1: a)
      (r: ref a)
  : STGhost unit opened
      (pts_to r p0 v0 `star` pts_to r p1 v1)
      (fun _ -> pts_to r p0 v0 `star` pts_to r p1 v0)
      (requires True)
      (ensures fun _ -> v0 == v1)

val alloc (#a:Type) (x:a)
  : ST (ref a)
      emp 
      (fun r -> pts_to r full_perm x)
      (requires True)
      (ensures fun r -> not (is_null r))

/// Reads the value in reference [r], as long as it initially is valid
val read (#a:Type)
         (#p:perm)
         (#v:erased a)
         (r:ref a)
  : ST a
      (pts_to r p v)
      (fun x -> pts_to r p v)
      (requires True)
      (ensures fun x -> x == Ghost.reveal v)

/// Writes value [x] in the reference [r], as long as we have full ownership of [r]
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

/// Splits the permission on reference [r] into two.
/// This function is computationally irrelevant (it has effect SteelGhost)
val share (#a:Type0)
          (#uses:_)
          (#p:perm)
          (#v:erased a)
          (r:ref a)
  : STGhostT unit uses
      (pts_to r p v)
      (fun _ -> pts_to r (half_perm p) v `star` pts_to r (half_perm p) v)

/// Combines permissions on reference [r].
/// This function is computationally irrelevant (it has effect SteelGhost)
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

/// Atomic compare and swap on references.
val cas (#t:eqtype)
        (#uses:inames)
        (r:ref t)
        (v:Ghost.erased t)
        (v_old v_new:t)
  : STAtomicT (b:bool{b <==> (Ghost.reveal v == v_old)})
      uses
      (pts_to r full_perm v)
      (fun b -> if b then pts_to r full_perm v_new else pts_to r full_perm v)
