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
  returns res: (slice t & slice t)
  ensures
    (let (s1, s2) = res in
      pts_to s1 #p v1 **
      pts_to s2 #p v2 **
      S.is_split s s1 s2)
{
  assert pure (v1 `Seq.equal` Seq.slice (Seq.append v1 v2) 0 (SZ.v i));
  assert pure (v2 `Seq.equal` Seq.slice (Seq.append v1 v2) (SZ.v i) (Seq.length v1 + Seq.length v2));
  S.split s i;
}

inline_for_extraction
noextract
fn append_split_trade (#t: Type) (input: S.slice t) (#p: perm) (i: SZ.t)
    (#v1: Ghost.erased (Seq.seq t) { SZ.v i == Seq.length v1 })
    (#v2: Ghost.erased (Seq.seq t))
  requires pts_to input #p (v1 `Seq.append` v2)
  returns res: (slice t & slice t)
  ensures
    (let (s1, s2) = res in
      pts_to s1 #p v1 ** pts_to s2 #p v2 **
      trade (pts_to s1 #p v1 ** pts_to s2 #p v2)
        (pts_to input #p (v1 `Seq.append` v2)))
{
  let s = append_split input i;
  match s {
    s1, s2 -> {
      ghost fn aux ()
        requires S.is_split input s1 s2 ** (pts_to s1 #p v1 ** pts_to s2 #p v2)
        ensures pts_to input #p (v1 `Seq.append` v2)
      {
        S.join s1 s2 input
      };
      intro_trade _ _ _ aux;
      (s1, s2)
    }
  }
}

inline_for_extraction
noextract
fn split_trade (#t: Type) (s: S.slice t) (#p: perm) (i: SZ.t) (#v: Ghost.erased (Seq.seq t) { SZ.v i <= Seq.length v })
  requires pts_to s #p v
  returns res: (slice t & slice t)
  ensures
    (let (s1, s2) = res in
      let v1 = Seq.slice v 0 (SZ.v i) in
      let v2 = Seq.slice v (SZ.v i) (Seq.length v) in
      pts_to s1 #p v1 ** pts_to s2 #p v2 **
      trade (pts_to s1 #p v1 ** pts_to s2 #p v2)
        (pts_to s #p v))
{
  Seq.lemma_split v (SZ.v i);
  let s' = S.split s i;
  match s' {
    s1, s2 -> {
      with v1 v2. assert pts_to s1 #p v1 ** pts_to s2 #p v2;
      ghost fn aux ()
        requires S.is_split s s1 s2 ** (pts_to s1 #p v1 ** pts_to s2 #p v2)
        ensures pts_to s #p v
      {
        S.join s1 s2 s
      };
      intro_trade _ _ _ aux;
      (s1, s2)
    }
  }
}

ghost fn ghost_append_split (#t: Type) (s: S.slice t) (#p: perm) (i: SZ.t)
    (#v1: (Seq.seq t) { SZ.v i == Seq.length v1 })
    (#v2: (Seq.seq t))
  requires pts_to s #p (v1 `Seq.append` v2)
  returns res: Ghost.erased (slice t & slice t)
  ensures
    (
      pts_to (fst res) #p v1 **
      pts_to (snd res) #p v2 **
      S.is_split s (fst res) (snd res)
    )
{
  assert pure (v1 `Seq.equal` Seq.slice (Seq.append v1 v2) 0 (SZ.v i));
  assert pure (v2 `Seq.equal` Seq.slice (Seq.append v1 v2) (SZ.v i) (Seq.length v1 + Seq.length v2));
  S.ghost_split s i
}

ghost fn ghost_append_split_trade (#t: Type) (input: S.slice t) (#p: perm) (i: SZ.t)
    (#v1: (Seq.seq t) { SZ.v i == Seq.length v1 })
    (#v2: (Seq.seq t))
  requires pts_to input #p (v1 `Seq.append` v2)
  returns res: Ghost.erased (slice t & slice t)
  ensures
    (
      pts_to (fst res) #p v1 ** pts_to (snd res) #p v2 **
      trade (pts_to (fst res) #p v1 ** pts_to (snd res) #p v2)
        (pts_to input #p (v1 `Seq.append` v2)))
{
  let res = ghost_append_split input i;
      ghost fn aux ()
        requires S.is_split input (fst res) (snd res) ** (pts_to (fst res) #p v1 ** pts_to (snd res) #p v2)
        ensures pts_to input #p (v1 `Seq.append` v2)
      {
        S.join (fst res) (snd res) input
      };
      intro_trade _ _ _ aux;
      res
}

ghost fn ghost_split_trade (#t: Type) (s: S.slice t) (#p: perm) (i: SZ.t) (#v: (Seq.seq t) { SZ.v i <= Seq.length v })
  requires pts_to s #p v
  returns res: Ghost.erased (slice t & slice t)
  ensures
    (
      let v1 = Seq.slice v 0 (SZ.v i) in
      let v2 = Seq.slice v (SZ.v i) (Seq.length v) in
      pts_to (fst res) #p v1 ** pts_to (snd res) #p v2 **
      trade (pts_to (fst res) #p v1 ** pts_to (snd res) #p v2)
        (pts_to s #p v))
{
  Seq.lemma_split v (SZ.v i);
  let s' = S.ghost_split s i;
      with v1 v2. assert pts_to (fst s') #p v1 ** pts_to (snd s') #p v2;
      ghost fn aux ()
        requires S.is_split s (fst s') (snd s') ** (pts_to (fst s') #p v1 ** pts_to (snd s') #p v2)
        ensures pts_to s #p v
      {
        S.join (fst s') (snd s') s
      };
      intro_trade _ _ _ aux;
      s'
}

inline_for_extraction
noextract
fn subslice_trade_mut #t (s: slice t) (i j: SZ.t) (#v: erased (Seq.seq t) { SZ.v i <= SZ.v j /\ SZ.v j <= Seq.length v })
  requires pts_to s v
  returns res: slice t
  ensures pts_to res (Seq.slice v (SZ.v i) (SZ.v j)) **
    (forall* v'. trade (pts_to res v') (pts_to s (Seq.slice v 0 (SZ.v i) `Seq.append` v' `Seq.append` Seq.slice v (SZ.v j) (Seq.length v))))
{
  let res = subslice s i j;
  ghost fn aux (v': Seq.seq t) ()
    requires subslice_rest res s 1.0R i j v ** pts_to res v'
    ensures pts_to s (Seq.slice v 0 (SZ.v i) `Seq.append` v' `Seq.append` Seq.slice v (SZ.v j) (Seq.length v))
  {
    unfold subslice_rest;
    join res _ _;
    join _ _ s;
    assert pure (
      Seq.Base.append (Seq.Base.append (Seq.Base.slice v 0 (SZ.v i)) v')
            (Seq.Base.slice v (SZ.v j) (Seq.Base.length v))
      `Seq.equal`
      Seq.Base.append (Seq.Base.slice v 0 (SZ.v i))
          (Seq.Base.append v' (Seq.Base.slice v (SZ.v j) (Seq.Base.length v))));
  };
  intro_forall _ (fun v' -> intro_trade _ _ _ (aux v'));
  res
}

inline_for_extraction
noextract
fn subslice_trade #t (s: slice t) #p (i j: SZ.t) (#v: erased (Seq.seq t) { SZ.v i <= SZ.v j /\ SZ.v j <= Seq.length v })
  requires pts_to s #p v
  returns res: slice t
  ensures pts_to res #p (Seq.slice v (SZ.v i) (SZ.v j)) **
    trade (pts_to res #p (Seq.slice v (SZ.v i) (SZ.v j))) (pts_to s #p v)
{
  let res = subslice s i j;
  ghost fn aux ()
    requires subslice_rest res s p i j v ** pts_to res #p (Seq.slice v (SZ.v i) (SZ.v j))
    ensures pts_to s #p v
  {
    unfold subslice_rest;
    join res _ _;
    join _ _ s;
    assert pure (v `Seq.equal` Seq.append (Seq.slice v 0 (SZ.v i))
      (Seq.append (Seq.slice v (SZ.v i) (SZ.v j)) (Seq.slice v (SZ.v j) (Seq.length v))));
  };
  intro_trade _ _ _ aux;
  res
}

(* BEGIN C only (see comment in Pulse.Lib.Slice) *)

module AP = Pulse.Lib.ArrayPtr

inline_for_extraction
fn arrayptr_to_slice_intro_trade
  (#t: Type) (a: AP.ptr t) (#p: perm) (alen: SZ.t) (#v: Ghost.erased (Seq.seq t))
  requires
    (AP.pts_to a #p v ** pure (SZ.v alen == Seq.length v))
  returns s: slice t
  ensures
    (pts_to s #p v **
      trade
        (pts_to s #p v)
        (AP.pts_to a #p v)
    )
{
  let s = arrayptr_to_slice_intro a alen;
  ghost fn aux (_: unit)
    requires arrayptr_to_slice a s ** pts_to s #p v
    ensures AP.pts_to a #p v
  {
    arrayptr_to_slice_elim s
  };
  intro_trade _ _ _ aux;
  s
}

inline_for_extraction
fn slice_to_arrayptr_intro_trade
  (#t: Type) (s: slice t) (#p: perm) (#v: Ghost.erased (Seq.seq t))
requires
  (pts_to s #p v)
  returns a: AP.ptr t
ensures
  (AP.pts_to a #p v **
    trade
      (AP.pts_to a #p v)
      (pts_to s #p v)
  )
{
  pts_to_len s;
  let a = slice_to_arrayptr_intro s;
  ghost fn aux (_: unit)
    requires slice_to_arrayptr s a ** AP.pts_to a #p v
    ensures pts_to s #p v
  {
    slice_to_arrayptr_elim a;
  };
  intro_trade _ _ _ aux;
  a
}

(* END C only *)
