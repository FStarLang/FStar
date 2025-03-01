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

module Pulse.Lib.Box
#lang-pulse

open FStar.Ghost
open PulseCore.FractionalPermission

open Pulse.Lib.Core
open Pulse.Class.PtsTo

module T = FStar.Tactics.V2

module R = Pulse.Lib.Reference

new
val box ([@@@strictly_positive] a:Type0) : Type0

val pts_to (#a:Type0)
           ([@@@mkey] b:box a)
           (#[T.exact (`1.0R)] p:perm)
           (v:a) : slprop

[@@pulse_unfold]
instance has_pts_to_box (a:Type u#0) : has_pts_to (box a) a = {
  pts_to = pts_to;
}

val pts_to_timeless (#a:Type) ([@@@mkey]r:box a) (p:perm) (x:a)
  : Lemma (timeless (pts_to r #p x))
          [SMTPat (timeless (pts_to r #p x))]

val alloc (#a:Type0) (x:a)
  : stt (box a) emp (fun b -> pts_to b x)
  
val ( ! ) (#a:Type0) (b:box a) (#v:erased a) (#p:perm)
  : stt a
      (pts_to b #p v)
      (fun x -> pts_to b #p v ** pure (eq2 #a (reveal v) x))

val ( := ) (#a:Type0) (b:box a) (x:a) (#v:erased a)
  : stt unit
      (pts_to b v) 
      (fun _ -> pts_to b (hide x))

val free (#a:Type0) (b:box a) (#v:erased a)
  : stt unit (pts_to b v) (fun _ -> emp)

val share (#a:Type) (r:box a) (#v:erased a) (#p:perm)
  : stt_ghost unit emp_inames
      (pts_to r #p v)
      (fun _ ->
       pts_to r #(p /. 2.0R) v **
       pts_to r #(p /. 2.0R) v)

[@@allow_ambiguous]
val gather (#a:Type) (r:box a) (#x0 #x1:erased a) (#p0 #p1:perm)
  : stt_ghost unit emp_inames
      (pts_to r #p0 x0 ** pts_to r #p1 x1)
      (fun _ -> pts_to r #(p0 +. p1) x0 ** pure (x0 == x1))

[@@allow_ambiguous]
val pts_to_injective_eq (#a:_)
                        (#p #q:_)
                        (#v0 #v1:a)
                        (r:box a)
  : stt_ghost unit emp_inames
      (pts_to r #p v0 ** pts_to r #q v1)
      (fun _ -> pts_to r #p v0 ** pts_to r #q v1 ** pure (v0 == v1))

val box_to_ref  (#a:Type0) (b:box a) : R.ref a

val to_ref_pts_to (#a:Type0) (b:box a) (#p:perm) (#v:a)
  : stt_ghost unit emp_inames (pts_to b #p v) (fun _ -> R.pts_to (box_to_ref b) #p v)

val to_box_pts_to (#a:Type0) (b:box a) (#p:perm) (#v:a)
  : stt_ghost unit emp_inames (R.pts_to (box_to_ref b) #p v) (fun _ -> pts_to b #p v)
