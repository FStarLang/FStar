(*
   Copyright 2026 Microsoft Research

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
module Pulse.Extrinsic.ExamplePredicates
friend Pulse.Extrinsic.HeapLang.Logic
friend PulseCore.IndirectionTheorySep
friend PulseCore.Heap2
friend PulseCore.BaseHeapSig

module H = PulseCore.Heap
module H2 = PulseCore.Heap2
module S = PulseCore.IndirectionTheorySep
module C = Pulse.Extrinsic.HeapLang.Logic
module M = Pulse.Extrinsic.HeapLang.Memory
module P = Pulse.Extrinsic.HeapLang.Proof
module K = PulseCore.KnotInstantiation

let bit_base (r:H.core_ref) =
  H2.h_exists (fun (n:bit) -> H2.pts_to #M.cell_value #M.cell_pcm r (M.Full n))

let bit_cell r = S.lift (bit_base r)

let bit_cell_unfold r =
  K.mem_pred_ext (bit_cell r) (S.op_exists_Star (bit_point r)) (fun h ->
    assert_norm (bit_cell r h == (exists (n:bit). C.points_to r n h));
    assert_norm (S.op_exists_Star (bit_point r) h == (exists (n:bit). C.points_to r n h)))

let bit_cell_intro r n =
  bit_cell_unfold r;
  S.implies_intro (C.points_to r n) (bit_cell r) (fun h ->
    introduce exists (v:bit). C.points_to r v h with n and ())

let bit_cell_exposed r =
  C.exposed_lift (bit_base r);
  S.timeless_lift (bit_base r);
  S.implies_intro (bit_cell r) (P.exposed (bit_cell r)) (fun _ -> S.reveal_slprop_ok ())
