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
module Pulse.Extrinsic.Ghost.Fractional

module G = Pulse.Extrinsic.Ghost
module F = Pulse.Lib.PCM.Fraction

let own #a g p x = G.own F.pcm_frac g (Some (x, p))
let alloc #a mask x =
  G.alloc mask F.pcm_frac (Some (x, 1.0R));
  assert_norm (allocated x == G.allocated F.pcm_frac (Some (x, 1.0R)))
let split #a g p q x = G.split F.pcm_frac g (Some (x, p)) (Some (x, q))
let agree #a g p q x y = G.compatible F.pcm_frac g (Some (x, p)) (Some (y, q))
let write #a mask g old desired =
  G.write mask F.pcm_frac g (Some (old, 1.0R)) (Some (desired, 1.0R))
    (F.mk_frame_preserving_upd old desired)
let exposed #a g p x = G.exposed F.pcm_frac g (Some (x, p))
