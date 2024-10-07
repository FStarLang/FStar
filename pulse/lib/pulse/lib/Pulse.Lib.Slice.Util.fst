module Pulse.Lib.Slice.Util
#lang-pulse
include Pulse.Lib.Pervasives
include Pulse.Lib.Slice
include Pulse.Lib.Trade

module S = Pulse.Lib.Slice
module SZ = FStar.SizeT
module T = FStar.Tactics

noextract
let append_split_precond
  (#t: Type) (mutb: bool) (p: perm) (v1: Ghost.erased (Seq.seq t)) (i: SZ.t)
: Tot prop
= SZ.v i == Seq.length v1 /\ (mutb == true ==> p == 1.0R)

let append_split_post'
    (#t: Type) (s: S.slice t) (p: perm) (v1 v2: Ghost.erased (Seq.seq t)) (i: SZ.t)
    (s1: S.slice t)
    (s2: S.slice t)
: Tot slprop
=
            S.pts_to s1 #p v1 **
            S.pts_to s2 #p v2 **
            S.is_split s p i s1 s2

let append_split_post
    (#t: Type) (s: S.slice t) (p: perm) (v1 v2: Ghost.erased (Seq.seq t)) (i: SZ.t)
    (res: S.slice_pair t)
: Tot slprop
= let S.SlicePair s1 s2 = res in
  append_split_post' s p v1 v2 i s1 s2

inline_for_extraction
noextract
fn append_split (#t: Type) (mutb: bool) (s: S.slice t) (#p: perm) (#v1 #v2: Ghost.erased (Seq.seq t)) (i: SZ.t)
    requires S.pts_to s #p (v1 `Seq.append` v2) ** pure (append_split_precond mutb p v1 i)
    returns res: S.slice_pair t
    ensures append_split_post  s p v1 v2 i res
{
  let vs = Ghost.hide (Seq.split (Seq.append v1 v2) (SZ.v i));
  assert (pure (fst vs `Seq.equal` v1));
  assert (pure (snd vs `Seq.equal` v2));
  let res = S.split mutb s i;
  match res {
    S.SlicePair s1 s2 -> {
      unfold (S.split_post s p (Seq.append v1 v2) i res);
      unfold (S.split_post' s p (Seq.append v1 v2) i s1 s2);
      fold (append_split_post' s p v1 v2 i s1 s2);
      fold (append_split_post s p v1 v2 i (S.SlicePair s1 s2));
      (S.SlicePair s1 s2)
    }
  }
}

let append_split_trade_post'
    (#t: Type) (s: S.slice t) (p: perm) (v1 v2: Ghost.erased (Seq.seq t)) (i: SZ.t)
    (s1: S.slice t)
    (s2: S.slice t)
: Tot slprop
=
            S.pts_to s1 #p v1 **
            S.pts_to s2 #p v2 **
            (trade (S.pts_to s1 #p v1 ** S.pts_to s2 #p v2) (S.pts_to s #p (v1 `Seq.append` v2)))

let append_split_trade_post
    (#t: Type) (s: S.slice t) (p: perm) (v1 v2: Ghost.erased (Seq.seq t)) (i: SZ.t)
    (res: S.slice_pair t)
: Tot slprop
= let S.SlicePair s1 s2 = res in
  append_split_trade_post' s p v1 v2 i s1 s2

ghost
fn append_split_trade_aux
  (#t: Type) (input: S.slice t) (p: perm) (v1 v2: (Seq.seq t)) (i: SZ.t) (input1 input2: S.slice t) (_: unit)
    requires S.is_split input p i input1 input2 ** (S.pts_to input1 #p v1 ** S.pts_to input2 #p v2)
    ensures S.pts_to input #p (v1 `Seq.append` v2)
{
  S.join input1 input2 input
}

inline_for_extraction
noextract
fn append_split_trade (#t: Type) (mutb: bool) (input: S.slice t) (#p: perm) (#v1 #v2: Ghost.erased (Seq.seq t)) (i: SZ.t)
    requires S.pts_to input #p (v1 `Seq.append` v2) ** pure (append_split_precond mutb p v1 i)
    returns res: S.slice_pair t
    ensures append_split_trade_post input p v1 v2 i res
{
  let res = append_split mutb input i;
  match res {
    S.SlicePair input1 input2 -> {
      unfold (append_split_post input p v1 v2 i res);
      unfold (append_split_post' input p v1 v2 i input1 input2);
      intro_trade _ _ _ (append_split_trade_aux input p v1 v2 i input1 input2);
      fold (append_split_trade_post' input p v1 v2 i input1 input2);
      fold (append_split_trade_post input p v1 v2 i (S.SlicePair input1 input2));
      (S.SlicePair input1 input2)
    }
  }
}

let split_trade_post'
    (#t: Type) (s: S.slice t) (p: perm) (v: Ghost.erased (Seq.seq t)) (i: SZ.t)
    (s1: S.slice t)
    (s2: S.slice t)
: Tot slprop
= exists* v1 v2 .
            S.pts_to s1 #p v1 **
            S.pts_to s2 #p v2 **
            (trade (S.pts_to s1 #p v1 ** S.pts_to s2 #p v2) (S.pts_to s #p v)) **
            pure (
                SZ.v i <= Seq.length v /\
                (v1, v2) == Seq.split v (SZ.v i)
            )

let split_trade_post
    (#t: Type) (s: S.slice t) (p: perm) (v: Ghost.erased (Seq.seq t)) (i: SZ.t)
    (res: S.slice_pair t)
: Tot slprop
= let (S.SlicePair s1 s2) = res in
  split_trade_post' s p v i s1 s2

ghost
fn split_trade_aux
  (#t: Type) (s: S.slice t) (p: perm) (v: Seq.seq t) (i: SZ.t)
  (s1 s2: S.slice t) (v1 v2: Seq.seq t) (hyp: squash (v == Seq.append v1 v2)) (_: unit)
    requires (S.is_split s p i s1 s2 ** (S.pts_to s1 #p v1 ** S.pts_to s2 #p v2))
    ensures (S.pts_to s #p v)
    {
      S.join s1 s2 s
    }

inline_for_extraction
noextract
fn split_trade (#t: Type) (mutb: bool) (s: S.slice t) (#p: perm) (#v: Ghost.erased (Seq.seq t)) (i: SZ.t)
    requires S.pts_to s #p v ** pure (S.split_precond mutb p v i)
    returns res: S.slice_pair t
    ensures split_trade_post s p v i res
{
  Seq.lemma_split v (SZ.v i);
  let res = S.split mutb s i;
  match res { S.SlicePair s1 s2 -> {
    unfold (S.split_post s p v i res);
    unfold (S.split_post' s p v i s1 s2);
    with v1 v2 . assert (S.pts_to s1 #p v1 ** S.pts_to s2 #p v2);
    intro_trade _ _ _ (split_trade_aux s p v i s1 s2 v1 v2 ());
    fold (split_trade_post' s p v i s1 s2);
    fold (split_trade_post s p v i (S.SlicePair s1 s2));
    (S.SlicePair s1 s2)
  }}
}
