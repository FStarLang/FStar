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

module Pulse.Lib.Swap.Slice
open Pulse.Lib.Pervasives
module SZ = FStar.SizeT
module S = Pulse.Lib.Slice

inline_for_extraction noextract [@@noextract_to "krml"]
val slice_swap
  (#t: Type0)
  (a: S.slice t)
  (mb: SZ.t)
  (#s: Ghost.erased (Seq.seq t))
: stt unit
  (
    pts_to a s **
    pure (SZ.v mb <= Seq.length s)
  )
  (fun mb' ->
    exists* s' .
    pts_to a s' **
    pure (
      SZ.v mb <= Seq.length s /\
      Seq.length s' == Seq.length s /\
      Seq.slice s' 0 (Seq.length s' - SZ.v mb) == Seq.slice s (SZ.v mb) (Seq.length s) /\
      Seq.slice s' (Seq.length s' - SZ.v mb) (Seq.length s') == Seq.slice s 0 (SZ.v mb)
    )
  )

inline_for_extraction noextract [@@noextract_to "krml"]
```pulse
fn slice_swap'
  (#t: Type0)
  (a: S.slice t)
  (mb: SZ.t)
  (s1: Ghost.erased (Seq.seq t))
  (s2: Ghost.erased (Seq.seq t))
requires
  pts_to a (Seq.append s1 s2) **
  pure (SZ.v mb == Seq.length s1)
ensures
  pts_to a (Seq.append s2 s1)
{
  S.pts_to_len a;
  slice_swap a mb;
  with s' . assert (pts_to a s');
  Seq.lemma_split s' (SZ.v (S.len a) - SZ.v mb);
  assert (pure (Seq.equal s' (Seq.append s2 s1)));
}
```
