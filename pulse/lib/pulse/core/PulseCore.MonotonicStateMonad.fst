(*
   Copyright 2024 Microsoft Research

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

module PulseCore.MonotonicStateMonad
open FStar.Preorder
module PST = PulseCore.PreorderStateMonad
let mst (#s:Type u#s)
         (rel:FStar.Preorder.preorder s)
         (a:Type u#a)
         (pre:s -> prop)
         (post:s -> a -> s -> prop)
  = PST.pst a rel pre post

let lift_pst
    (#s:Type u#s)
    (#rel:FStar.Preorder.preorder s)
    (#a:Type u#a)
    (#pre:s -> prop)
    (#post:s -> a -> s -> prop)
    (pst:PST.pst a rel pre post)
: mst rel a pre post
= pst

let return = PST.return
let bind = PST.bind
let weaken = PST.weaken
let get = PST.get
let put = PST.put

let witness p = admit()
let recall p w = admit()
let with_get #s #a #rel #req_f #ens_f f = fun m0 -> f m0 m0