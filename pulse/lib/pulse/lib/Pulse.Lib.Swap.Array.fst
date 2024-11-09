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

module Pulse.Lib.Swap.Array
#lang-pulse
module R = Pulse.Lib.Reference
module Prf = Pulse.Lib.Swap.Spec
open Pulse.Lib.Swap.Common
#set-options "--fuel 2 --ifuel 1"
#restart-solver

inline_for_extraction
let size_add
  (a: SZ.t)
  (b: SZ.t)
  (_: squash (SZ.fits (SZ.v a + SZ.v b)))
: Tot (c: SZ.t {
    SZ.v c == SZ.v a + SZ.v b
  })
= a `SZ.add` b

inline_for_extraction
let size_lt
  (a: SZ.t)
  (b: SZ.t)
: Tot (c: bool { c == (SZ.v a < SZ.v b) })
= a `SZ.lt` b

inline_for_extraction
let size_sub
  (a: SZ.t)
  (b: SZ.t)
  (_: squash (SZ.v a >= SZ.v b))
: Tot (c: SZ.t { SZ.v c == (SZ.v a - SZ.v b) })
= a `SZ.sub` b

#restart-solver

#push-options "--z3rlimit_factor 4"

inline_for_extraction noextract [@@noextract_to "krml"]

fn array_swap_aux(#t: Type0) (a: A.array t) (lb: SZ.t) (rb: SZ.t) (mb: (mb: SZ.t {SZ.v mb > SZ.v lb /\ SZ.v mb < SZ.v rb})) (bz: Prf.bezout (SZ.v rb - SZ.v lb) (SZ.v mb - SZ.v lb)) (d: SZ.t) (q: SZ.t) (#s0: Ghost.erased (Seq.seq t))
  requires (
    A.pts_to_range a (Ghost.reveal (SZ.v lb)) (Ghost.reveal (SZ.v rb)) s0 **
    pure (
      SZ.v d == bz.d /\
      SZ.v q == bz.q_n
    )
  )
  ensures exists* s . (
    A.pts_to_range a (Ghost.reveal (SZ.v lb)) (Ghost.reveal (SZ.v rb)) s **
    pure (Prf.array_swap_post s0 (SZ.v rb - SZ.v lb) (SZ.v mb - SZ.v lb) s) // hoisted out because of the SMT pattern on array_as_ring_buffer_swap
  )
{   
    A.pts_to_range_prop a;
    let mut pi = lb;
    while (let i = !pi; ((i `SZ.sub` lb) `size_lt` d))
    invariant b . exists* s i . (
      A.pts_to_range a (Ghost.reveal (SZ.v lb)) (Ghost.reveal (SZ.v rb)) s **
      pts_to pi i **
      pure (
        SZ.v i >= SZ.v lb /\
        SZ.v i < SZ.v rb /\
        Prf.array_swap_outer_invariant s0 (SZ.v rb - SZ.v lb) (SZ.v mb - SZ.v lb) bz s (SZ.v i - SZ.v lb) /\
        b == (SZ.v i - SZ.v lb < bz.d)
    )) {
      let i = !pi;
      let save = A.pts_to_range_index a i;
      let mut pj = 0sz;
      let mut pidx = i;
      while (let j = !pj; (j `size_lt` (size_sub q 1sz ())))
      invariant b . exists* s j idx . (
        A.pts_to_range a (Ghost.reveal (SZ.v lb)) (Ghost.reveal (SZ.v rb)) s **
        pts_to pi i **
        pts_to pj j **
        pts_to pidx idx **
        pure (
          SZ.v idx >= SZ.v lb /\
          SZ.v idx < SZ.v rb /\
          Prf.array_swap_inner_invariant s0 (SZ.v rb - SZ.v lb) (SZ.v mb - SZ.v lb) bz s (SZ.v i - SZ.v lb) (SZ.v j) (SZ.v idx - SZ.v lb) /\
          b == (SZ.v j < bz.q_n - 1)
        )
      ) {
        let j = !pj;
        let idx = !pidx;
        let idx' = impl_jump lb rb mb idx ();
        let x = A.pts_to_range_index a idx';
        let j' = size_add j 1sz ();
        A.pts_to_range_upd a idx x;
        pj := j';
        pidx := idx';
        ()
      };
      ();
      let idx = !pidx;
      A.pts_to_range_upd a idx save;
      let i' = size_add i 1sz ();
      pi := i';
      ()
    };
    ()
}


#pop-options

let intro_array_swap_post1 (lb rb mb:SZ.t) (mb':SZ.t)
  : Lemma (requires SZ.v lb <= SZ.v mb /\ SZ.v mb <= SZ.v rb /\ lb == mb /\ mb' == rb)
          (ensures array_swap_post lb rb mb mb') = ()

let intro_array_swap_post2 (lb rb mb:SZ.t) (mb':SZ.t)
  : Lemma (requires SZ.v lb <= SZ.v mb /\ SZ.v mb <= SZ.v rb /\ mb == rb /\ mb' == lb)
          (ensures array_swap_post lb rb mb mb') = ()

#push-options "--fuel 0 --ifuel 0 --split_queries no"
inline_for_extraction noextract [@@noextract_to "krml"]

fn array_swap
  (#t: Type0)
  (a: A.array t)
  (lb: SZ.t) (rb: SZ.t)
  (mb: SZ.t)
  (#s1 #s2: Ghost.erased (Seq.seq t))
requires (
    A.pts_to_range a (SZ.v lb) (SZ.v mb) s1 **
    A.pts_to_range a (SZ.v mb) (SZ.v rb) s2
  )
returns mb' : SZ.t
ensures (
    A.pts_to_range a (SZ.v lb) (SZ.v mb') s2 **
    A.pts_to_range a (SZ.v mb') (SZ.v rb) s1 **
    pure (array_swap_post lb rb mb mb')
  )
{
  A.pts_to_range_prop a #(SZ.v lb) #(SZ.v mb);
  A.pts_to_range_prop a #(SZ.v mb) #(SZ.v rb);
  A.pts_to_range_join a (SZ.v lb) (SZ.v mb) (SZ.v rb);
  with s . assert (A.pts_to_range a (SZ.v lb) (SZ.v rb) s);
  if (lb = mb) {
    let prf_s1 : squash (s1 `Seq.equal` Seq.empty) = ();
    let prf_s : squash (s2 `Seq.equal` s) = ();
    A.pts_to_range_split a (SZ.v lb) (SZ.v rb) (SZ.v rb);
    with s2' . assert (A.pts_to_range a (SZ.v lb) (SZ.v rb) s2');
    with s1' . assert (A.pts_to_range a (SZ.v rb) (SZ.v rb) s1');
    let prf1 : squash (s1' `Seq.equal` s1) = ();
    let prf2 : squash (s2' `Seq.equal` s2) = ();
    rewrite (A.pts_to_range a (SZ.v lb) (SZ.v rb) s2')
         as (A.pts_to_range a (SZ.v lb) (SZ.v rb) s2);
    rewrite (A.pts_to_range a (SZ.v rb) (SZ.v rb) s1')
         as (A.pts_to_range a (SZ.v rb) (SZ.v rb) s1);
    let _p : squash (array_swap_post lb rb mb rb) = intro_array_swap_post1 lb rb mb rb;
    rb
  } else if (mb = rb) {
    let prf_s2 : squash (s2 `Seq.equal` Seq.empty) = ();
    let prf_s : squash (s1 `Seq.equal` s) = ();
    A.pts_to_range_split a (SZ.v lb) (SZ.v lb) (SZ.v rb);
    with s2' . assert (A.pts_to_range a (SZ.v lb) (SZ.v lb) s2');
    assert (A.pts_to_range a (SZ.v lb) (SZ.v lb) s2');
    with s1' . assert (A.pts_to_range a (SZ.v lb) (SZ.v rb) s1');
    assert (A.pts_to_range a (SZ.v lb) (SZ.v rb) s1');
    let prf1 : squash (s1' `Seq.equal` s1) = ();
    let prf2 : squash (s2' `Seq.equal` s2) = ();
    rewrite (A.pts_to_range a (SZ.v lb) (SZ.v lb) s2')
         as (A.pts_to_range a (SZ.v lb) (SZ.v lb) s2);
    rewrite (A.pts_to_range a (SZ.v lb) (SZ.v rb) s1')
         as (A.pts_to_range a (SZ.v lb) (SZ.v rb) s1);
    let prf_mb : squash (array_swap_post lb rb mb lb) = intro_array_swap_post2 lb rb mb lb;
    lb
  } else {
    Seq.lemma_split s (SZ.v mb - SZ.v lb);
    Seq.lemma_append_inj s1 s2 (Seq.slice s 0 (SZ.v mb - SZ.v lb)) (Seq.slice s (SZ.v mb - SZ.v lb) (Seq.length s));
    rewrite (A.pts_to_range a (SZ.v lb) (SZ.v rb) s)
      as (A.pts_to_range a (Ghost.reveal (SZ.v lb)) (Ghost.reveal (SZ.v rb)) s);
    let d = gcd (rb `SZ.sub` lb) (mb `SZ.sub` lb);
    let q = (rb `SZ.sub` lb) `SZ.div` d;
    array_swap_aux a lb rb mb (Prf.mk_bezout _ _) d q;
    with s' . assert (A.pts_to_range a (Ghost.reveal (SZ.v lb)) (Ghost.reveal (SZ.v rb)) s');
    rewrite (A.pts_to_range a (Ghost.reveal (SZ.v lb)) (Ghost.reveal (SZ.v rb)) s')
      as (A.pts_to_range a (SZ.v lb) (SZ.v rb) s');
    Seq.lemma_split s' (SZ.v rb - SZ.v mb);
    Seq.lemma_append_inj s2 s1 (Seq.slice s' 0 (SZ.v rb - SZ.v mb)) (Seq.slice s' (SZ.v rb - SZ.v mb) (Seq.length s'));
    let mb' = (lb `SZ.add` (rb `SZ.sub` mb));
    A.pts_to_range_split a (SZ.v lb) (SZ.v mb') (SZ.v rb);
    with s2' . assert (A.pts_to_range a (SZ.v lb) (SZ.v mb') s2');
    rewrite (A.pts_to_range a (SZ.v lb) (SZ.v mb') s2')
      as (A.pts_to_range a (SZ.v lb) (SZ.v mb') s2);
    with s1' . assert (A.pts_to_range a (SZ.v mb') (SZ.v rb) s1');
    rewrite (A.pts_to_range a (SZ.v mb') (SZ.v rb) s1')
      as (A.pts_to_range a (SZ.v mb') (SZ.v rb) s1);
    mb'
  }
}

#pop-options
