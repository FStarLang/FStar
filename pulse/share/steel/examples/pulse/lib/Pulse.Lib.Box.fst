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

open Pulse.Lib.Core

module R = Pulse.Lib.Reference

type box a = R.ref a
let pts_to b #p v = R.pts_to b #p v
let alloc x = R.alloc x
let op_Bang b = R.op_Bang b 
let op_Colon_Equals b x = R.op_Colon_Equals b x
let free b = R.free b

let box_to_ref b = b

let to_ref_pts_to #a b #p #v =
  rewrite (pts_to b #p v) (R.pts_to b #p v) (vprop_equiv_refl _)

let to_box_pts_to #a r #p #v =
  rewrite (R.pts_to r #p v) (pts_to r #p v) (vprop_equiv_refl _)
