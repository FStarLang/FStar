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

module Pulse.Lib.Slice.Util
#lang-pulse
include Pulse.Lib.Pervasives
include Pulse.Lib.Slice
include Pulse.Lib.Trade

module S = Pulse.Lib.Slice
module SZ = FStar.SizeT

inline_for_extraction
noextract
fn append_split (#t: Type) (s: S.slice t) (#p: perm) (i: SZ.t)
    (#v1: Ghost.erased (Seq.seq t) { SZ.v i == Seq.length v1 })
    (#v2: Ghost.erased (Seq.seq t))
  requires pts_to s #p (v1 `Seq.append` v2)
  returns res: S.slice_pair t
  ensures
    (let S.SlicePair s1 s2 = res in
      pts_to s1 #p v1 **
      pts_to s2 #p v2 **
      S.is_split s s1 s2)
{
  assert pure (v1 `Seq.equal` Seq.slice (Seq.append v1 v2) 0 (SZ.v i));
  assert pure (v2 `Seq.equal` Seq.slice (Seq.append v1 v2) (SZ.v i) (Seq.length v1 + Seq.length v2));
  S.split s i
}

ghost
fn append_split_trade_aux
  (#t: Type) (input: S.slice t) (p: perm) (v1 v2: (Seq.seq t)) (i: SZ.t) (input1 input2: S.slice t) (_: unit)
    requires S.is_split input input1 input2 ** (pts_to input1 #p v1 ** pts_to input2 #p v2)
    ensures pts_to input #p (v1 `Seq.append` v2)
{
  S.join input1 input2 input
}

inline_for_extraction
noextract
fn append_split_trade (#t: Type) (input: S.slice t) (#p: perm) (i: SZ.t)
    (#v1: Ghost.erased (Seq.seq t) { SZ.v i == Seq.length v1 })
    (#v2: Ghost.erased (Seq.seq t))
  requires pts_to input #p (v1 `Seq.append` v2)
  returns res: S.slice_pair t
  ensures
    (let SlicePair s1 s2 = res in
      pts_to s1 #p v1 ** pts_to s2 #p v2 **
      trade (pts_to s1 #p v1 ** pts_to s2 #p v2)
        (pts_to input #p (v1 `Seq.append` v2)))
{
  let SlicePair s1 s2 = append_split input i;
  intro_trade _ _ _ (append_split_trade_aux input p v1 v2 i s1 s2);
  SlicePair s1 s2
}

ghost
fn split_trade_aux
  (#t: Type) (s: S.slice t) (p: perm) (v: Seq.seq t) (i: SZ.t)
  (s1 s2: S.slice t) (v1 v2: Seq.seq t) (hyp: squash (v == Seq.append v1 v2)) (_: unit)
    requires (S.is_split s s1 s2 ** (pts_to s1 #p v1 ** pts_to s2 #p v2))
    ensures (pts_to s #p v)
{
  S.join s1 s2 s
}

inline_for_extraction
noextract
fn split_trade (#t: Type) (s: S.slice t) (#p: perm) (i: SZ.t) (#v: Ghost.erased (Seq.seq t) { SZ.v i <= Seq.length v })
  requires pts_to s #p v
  returns res: S.slice_pair t
  ensures
    (let SlicePair s1 s2 = res in
      let v1 = Seq.slice v 0 (SZ.v i) in
      let v2 = Seq.slice v (SZ.v i) (Seq.length v) in
      pts_to s1 #p v1 ** pts_to s2 #p v2 **
      trade (pts_to s1 #p v1 ** pts_to s2 #p v2)
        (pts_to s #p (v1 `Seq.append` v2)))
{
  Seq.lemma_split v (SZ.v i);
  let SlicePair s1 s2 = S.split s i;
  with v1 v2. assert pts_to s1 #p v1 ** pts_to s2 #p v2;
  intro_trade _ _ _ (split_trade_aux s p v i s1 s2 v1 v2 ());
  S.SlicePair s1 s2
}
