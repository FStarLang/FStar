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
module Pulse.Extrinsic.Ghost

open FStar.PCM
module S = PulseCore.IndirectionTheorySep
module P = Pulse.Extrinsic.HeapLang.Proof

let name = PulseCore.MemoryAlt.core_ghost_ref
val own (#a:Type0) (pcm:pcm a) (g:name) (x:a) : S.slprop
let allocated (#a:Type0) (pcm:pcm a) (x:a) =
  S.op_exists_Star (fun (g:name) -> own pcm g x)

val alloc (#a:Type0) (mask:S.inames) (pcm:pcm a) (x:a{pcm.refine x})
  : Lemma (P.update mask mask S.emp (allocated pcm x))
val write (#a:Type0) (mask:S.inames) (pcm:pcm a) (g:name) (x y:a)
  (upd:frame_preserving_upd pcm x y)
  : Lemma (P.update mask mask (own pcm g x) (own pcm g y))
val split (#a:Type0) (pcm:pcm a) (g:name) (x:a) (y:a{composable pcm x y})
  : Lemma (own pcm g (op pcm x y) == S.star (own pcm g x) (own pcm g y))
val compatible (#a:Type0) (pcm:pcm a) (g:name) (x y:a)
  : Lemma (S.implies (S.star (own pcm g x) (own pcm g y))
      (S.pure (composable pcm x y)))
val exposed (#a:Type0) (pcm:pcm a) (g:name) (x:a)
  : Lemma (
      S.implies (P.exposed (own pcm g x)) (own pcm g x) /\
      S.implies (own pcm g x) (P.exposed (own pcm g x)))
