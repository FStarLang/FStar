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

module H = PulseCore.Heap
module S = PulseCore.IndirectionTheorySep
module C = Pulse.Extrinsic.HeapLang.Logic
module P = Pulse.Extrinsic.HeapLang.Proof

type bit = n:int{n == 0 \/ n == 1}
let bit_point (r:H.core_ref) (n:bit) = C.points_to r n
val bit_cell (r:H.core_ref) : S.slprop
val bit_cell_unfold (r:H.core_ref)
  : Lemma (bit_cell r == S.op_exists_Star (bit_point r))
val bit_cell_intro (r:H.core_ref) (n:bit)
  : Lemma (S.implies (C.points_to r n) (bit_cell r))
val bit_cell_exposed (r:H.core_ref)
  : Lemma (
      S.implies (P.exposed (bit_cell r)) (bit_cell r) /\
      S.implies (bit_cell r) (P.exposed (bit_cell r)))
