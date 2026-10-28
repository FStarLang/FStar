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

module Pulse.Lib.Vec
open Pulse.Class.PtsTo
open FStar.Ghost
open PulseCore.FractionalPermission
module SZ = FStar.SizeT
module Seq = FStar.Seq
#lang-pulse

open Pulse.Lib.Core
open Pulse.Lib.Pervasives

module R = Pulse.Lib.Reference
module A = Pulse.Lib.Array

type vec a = A.array a
let length v = A.length v
let is_full_vec v = A.is_full_array v
let pts_to v #p s = A.pts_to v #p s
let pts_to_timeless _ _ _ = ()
let pts_to_len v = A.pts_to_len v

(* This function is extracted primitively. The implementation
below is only a model, and uses the internal Ref.alloc. Hence
we disable the warning about using Array.alloc. *)
#push-options "--warn_error -288"
let alloc x n = A.alloc x n
#pop-options
let ( .() ) v i #p #s = A.op_Dot_Lparen_Rparen v i #p #s
let ( .()<- ) v i x #s = A.op_Dot_Lparen_Rparen_Less_Minus v i x #s
(* Same comment as above *)
#push-options "--warn_error -288"
let free v #s = A.free v #s
#pop-options
let share v = A.share v
let gather v = A.gather v

let vec_to_array v = v

ghost
fn to_array_pts_to (#a:Type0) (v:vec a) (#p:perm) (#s:Seq.seq a)
  requires pts_to v #p s
  ensures A.pts_to (vec_to_array v) #p s
{
  rewrite (pts_to v #p s) as
          (A.pts_to (vec_to_array v) #p s);
}

ghost
fn to_vec_pts_to (#a:Type0) (v:vec a) (#p:perm) (#s:Seq.seq a)
  requires A.pts_to (vec_to_array v) #p s
  ensures pts_to v #p s
{
   rewrite (A.pts_to (vec_to_array v) #p s)
        as (pts_to v #p s)

}
