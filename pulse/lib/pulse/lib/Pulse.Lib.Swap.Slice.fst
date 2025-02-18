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
#lang-pulse
module Prf = Pulse.Lib.Swap.Spec
open Pulse.Lib.Swap.Common
#set-options "--fuel 2 --ifuel 1"
#restart-solver

#push-options "--z3rlimit_factor 6"

#restart-solver

inline_for_extraction noextract [@@noextract_to "krml"]
fn slice_swap_aux(#t: Type0) (a: S.slice t) (mb: (mb: SZ.t {0 < SZ.v mb /\ SZ.v mb < SZ.v (S.len a)})) (bz: Prf.bezout (SZ.v (S.len a)) (SZ.v mb)) (d: SZ.t) (q: SZ.t) (#s0: Ghost.erased (Seq.seq t))
  requires (
    pts_to a s0 **
    pure (
      SZ.v d == bz.d /\
      SZ.v q == bz.q_n
    )
  )
  ensures exists* s . (
    pts_to a s **
    pure (Prf.array_swap_post s0 (SZ.v (S.len a)) (SZ.v mb) s) // hoisted out because of the SMT pattern on array_as_ring_buffer_swap
  )
{   
    S.pts_to_len a;
    let mut pi = 0sz;
    while (let i = !pi; (i `SZ.lt` d))
    invariant b . exists* s i . (
      pts_to a s **
      pts_to pi i **
      pure (
        Seq.length s == SZ.v (S.len a) /\
        SZ.v i < SZ.v (S.len a) /\
        Prf.array_swap_outer_invariant s0 (SZ.v (S.len a)) (SZ.v mb) bz s (SZ.v i) /\
        b == (SZ.v i < bz.d)
    )) {
      let i = !pi;
      let save = S.op_Array_Access a i;
      let mut pj = 0sz;
      let mut pidx = i;
      while (let j = !pj; (SZ.lt j (SZ.sub q 1sz)))
      invariant b . exists* s j idx . (
        pts_to a s **
        pts_to pi i **
        pts_to pj j **
        pts_to pidx idx **
        pure (
          Seq.length s == SZ.v (S.len a) /\
          SZ.v idx < SZ.v (S.len a) /\
          Prf.array_swap_inner_invariant s0 (SZ.v (S.len a)) (SZ.v mb) bz s (SZ.v i) (SZ.v j) (SZ.v idx) /\
          b == (SZ.v j < bz.q_n - 1)
        )
      ) {
        let j = !pj;
        let idx = !pidx;
        let idx' = impl_jump 0sz (S.len a) mb idx ();
        let x = S.op_Array_Access a idx';
        let j' = SZ.add j 1sz;
        S.op_Array_Assignment a idx x;
        pj := j';
        pidx := idx';
        ()
      };
      ();
      with s . assert (pts_to a s);
      with j . assert (pts_to pj j);
      let idx = !pidx;
      S.op_Array_Assignment a idx save;
      let i' = SZ.add i 1sz;
      pi := i';
      ()
    };
    ()
}

#pop-options

#push-options "--fuel 0 --ifuel 0 --split_queries no"
inline_for_extraction noextract [@@noextract_to "krml"]
fn slice_swap0
  (#t: Type0)
  (a: S.slice t)
  (mb: SZ.t)
  (#s: Ghost.erased (Seq.seq t))
requires (
    pts_to a s **
    pure (SZ.v mb <= Seq.length s)
  )
ensures (
    exists* s' .
    pts_to a s' **
    pure (
      SZ.v mb <= Seq.length s /\
      Seq.length s' == Seq.length s /\
      Seq.equal (Seq.slice s' 0 (Seq.length s' - SZ.v mb)) (Seq.slice s (SZ.v mb) (Seq.length s)) /\
      Seq.equal (Seq.slice s' (Seq.length s' - SZ.v mb) (Seq.length s')) (Seq.slice s 0 (SZ.v mb))
    )
  )
{
  S.pts_to_len a;
  if (mb = 0sz || mb = S.len a) {
    ()
  } else {
    Seq.lemma_split s (SZ.v mb);
    let d = gcd (S.len a) (mb);
    let q = (S.len a) `SZ.div` d;
    slice_swap_aux a mb (Prf.mk_bezout _ _) d q;
  }
}

#pop-options

inline_for_extraction noextract [@@noextract_to "krml"]
fn slice_swap
  (#t: Type0)
  (a: S.slice t)
  (mb: SZ.t)
  (#s: Ghost.erased (Seq.seq t))
requires (
    pts_to a s **
    pure (SZ.v mb <= Seq.length s)
  )
ensures (
    exists* s' .
    pts_to a s' **
    pure (
      SZ.v mb <= Seq.length s /\
      Seq.length s' == Seq.length s /\
      (Seq.slice s' 0 (Seq.length s' - SZ.v mb)) == (Seq.slice s (SZ.v mb) (Seq.length s)) /\
      (Seq.slice s' (Seq.length s' - SZ.v mb) (Seq.length s')) == (Seq.slice s 0 (SZ.v mb))
    )
  )
{
  slice_swap0 a mb
}
