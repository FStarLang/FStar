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
module Steel.ST.GhostReference
open FStar.Ghost
open Steel.ST.Util
open Steel.ST.Coercions
module R = Steel.Reference

[@@ erasable]
let ref (a:Type u#0)
  : Type u#0
  = R.ghost_ref a

let pts_to (#a:_)
           (r:ref a)
           (p:perm)
           ([@@@smt_fallback] v:a)
  : vprop
  = R.ghost_pts_to r p v

let pts_to_injective_eq (#a:_)
                        (#u:_)
                        (#p #q:_)
                        (#v0 #v1:a)
                        (r:ref a)
  : STGhost unit u
      (pts_to r p v0 `star` pts_to r q v1)
      (fun _ -> pts_to r p v0 `star` pts_to r q v0)
      (requires True)
      (ensures fun _ -> v0 == v1)
  = coerce_ghost
    (fun _ -> R.ghost_pts_to_injective_eq #a #u #p #q r (hide v0) (hide v1))

let pts_to_perm r = coerce_ghost (fun _ -> R.ghost_pts_to_perm r)

let alloc (#a:Type)
          (#u:_)
          (x:erased a)
  : STGhostT (ref a) u
      emp
      (fun r -> pts_to r full_perm x)
  = coerce_ghost (fun _ -> R.ghost_alloc_pt x)

let read (#a:Type)
         (#u:_)
         (#p:perm)
         (#v:erased a)
         (r:ref a)
  : STGhost (erased a) u
      (pts_to r p v)
      (fun x -> pts_to r p x)
      (requires True)
      (ensures fun x -> x == v)
  = let y = coerce_ghost (fun _ -> R.ghost_read_pt r) in
    y

let write (#a:Type)
          (#u:_)
          (#v:erased a)
          (r:ref a)
          (x:erased a)
  : STGhostT unit u
      (pts_to r full_perm v)
      (fun _ -> pts_to r full_perm x)
  = coerce_ghost (fun _ -> R.ghost_write_pt r x)

let share (#a:Type)
          (#u:_)
          (#p:perm)
          (#x:erased a)
          (r:ref a)
  : STGhostT unit u
      (pts_to r p x)
      (fun _ -> pts_to r (half_perm p) x `star`
             pts_to r (half_perm p) x)
  = coerce_ghost (fun _ -> R.ghost_share_pt r)

let gather (#a:Type)
           (#u:_)
           (#p0 #p1:perm)
           (#x0 #x1:erased a)
           (r:ref a)
  : STGhost unit u
      (pts_to r p0 x0 `star` pts_to r p1 x1)
      (fun _ -> pts_to r (sum_perm p0 p1) x0)
      (requires True)
      (ensures fun _ -> x0 == x1)
  = coerce_ghost (fun _ -> R.ghost_gather_pt #a #u #p0 #p1 #x0 #x1 r)

let free (#a:Type0)
         (#u:_)
         (#v:erased a)
         (r:ref a)
  : STGhostT unit u
      (pts_to r full_perm v)
      (fun _ -> emp)
  = coerce_ghost (fun _ -> R.ghost_free_pt r)
