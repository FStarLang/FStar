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
module Pulse.Extrinsic.GhostExamples

open FStar.Real
module P = Pulse.Extrinsic.HeapLang.Proof
module S = PulseCore.IndirectionTheorySep
module G = Pulse.Extrinsic.Ghost
module F = Pulse.Extrinsic.Ghost.Fractional
module R = Pulse.Extrinsic.Rules

let advance (mask:S.inames) (g:G.name) (old:int)
  : Lemma (P.update mask mask
      (S.star (F.own g 0.5R old) (F.own g 0.5R old))
      (S.star (F.own g 0.5R (old + 1)) (F.own g 0.5R (old + 1))))
  = F.split g 0.5R 0.5R old;
    F.write mask g old (old + 1);
    F.split g 0.5R 0.5R (old + 1)

let agree (g:G.name) (mine theirs:int)
  : Lemma (S.implies (S.star (F.own g 0.5R mine) (F.own g 0.5R theirs))
      (S.pure (mine == theirs)))
  = F.agree g 0.5R 0.5R mine theirs;
    R.entails_pure
      (mine == theirs /\ 0.5R +. 0.5R <=. 1.0R)
      (mine == theirs);
    R.entails_trans
      (S.star (F.own g 0.5R mine) (F.own g 0.5R theirs))
      (S.pure (mine == theirs /\ 0.5R +. 0.5R <=. 1.0R))
      (S.pure (mine == theirs))
