(*
   Copyright 2023 Microsoft Research

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

module Pulse.Lib.HigherGhostReference
open FStar.Tactics
open Pulse.Lib.Core
open PulseCore.FractionalPermission
open FStar.Ghost

[@@erasable]
val ref ([@@@unused] a:Type u#1) : Type u#0
      
instance val non_informative_gref (a:Type u#1)
  : NonInformative.non_informative (ref a)

val pts_to
  (#a:Type)
  ([@@@equate_strict] r:ref a)
  (#[exact (`1.0R)] p:perm)
  (n:a)
: slprop

val pts_to_is_slprop1 (#a:Type) (r:ref a) (p:perm) (n:a)
  : Lemma (is_slprop1 (pts_to r #p n))

val alloc (#a:Type) (x:a)
  : stt_ghost (ref a) emp_inames emp (fun r -> pts_to r x)
  
val read (#a:Type) (r:ref a) (#n:erased a) (#p:perm)
  : stt_ghost (erased a) emp_inames
        (pts_to r #p n)
        (fun x -> pts_to r #p n ** pure (n == x))

val ( ! ) (#a:Type) (r:ref a) (#n:erased a) (#p:perm)
  : stt_ghost (erased a) emp_inames
        (pts_to r #p n)
        (fun x -> pts_to r #p n ** pure (n == x))


val ( := ) (#a:Type) (r:ref a) (x:erased a) (#n:erased a)
  : stt_ghost unit emp_inames
        (pts_to r n) 
        (fun _ -> pts_to r x)

let write = ( := )

val free (#a:Type) (r:ref a) (#n:erased a)
  : stt_ghost unit emp_inames (pts_to r n) (fun _ -> emp)

val share (#a:Type) (r:ref a) (#v:erased a) (#p:perm)
  : stt_ghost unit emp_inames
      (pts_to r #p v)
      (fun _ ->
       pts_to r #(p /. 2.0R) v **
       pts_to r #(p /. 2.0R) v)

[@@allow_ambiguous]
val gather (#a:Type) (r:ref a) (#x0 #x1:erased a) (#p0 #p1:perm)
  : stt_ghost unit emp_inames
      (pts_to r #p0 x0 ** pts_to r #p1 x1)
      (fun _ -> pts_to r #(p0 +. p1) x0 ** pure (x0 == x1))

(* Share/gather specialized to half permission *)
val share2 (#a:Type) (r:ref a) (#v:erased a)
  : stt_ghost unit emp_inames
      (pts_to r v)
      (fun _ -> pts_to r #0.5R v ** pts_to r #0.5R v)

[@@allow_ambiguous]
val gather2 (#a:Type) (r:ref a) (#x0 #x1:erased a)
  : stt_ghost unit emp_inames
      (pts_to r #0.5R x0 ** pts_to r #0.5R x1)
      (fun _ -> pts_to r x0 ** pure (x0 == x1))

[@@allow_ambiguous]
val pts_to_injective_eq (#a:_)
                        (#p #q:_)
                        (#v0 #v1:a)
                        (r:ref a)
  : stt_ghost unit emp_inames
      (pts_to r #p v0 ** pts_to r #q v1)
      (fun _ -> pts_to r #p v0 ** pts_to r #q v1 ** pure (v0 == v1))

val pts_to_perm_bound (#a:_) (#p:_) (r:ref a) (#v:a)
  : stt_ghost unit emp_inames
      (pts_to r #p v)
      (fun _ -> pts_to r #p v ** pure (p <=. 1.0R))
