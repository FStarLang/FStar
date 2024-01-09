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

module PulseTutorial.Algorithms

open FStar.Mul
open FStar.SizeT

open Pulse.Lib.Pervasives
open Pulse.Lib.Array

module SZ = FStar.SizeT
module G = FStar.Ghost
module R = Pulse.Lib.Reference

let count (#a:eqtype) (x:a) (s:Seq.seq a) (j:nat { j <= Seq.length s }) : GTot nat =
  Seq.count x (Seq.slice s 0 j)

let count_len (#a:eqtype) (x:a) (s:Seq.seq a) (j:nat { j <= Seq.length s })
  : Lemma (ensures count x s j <= j)
          [SMTPat (count x s j)] =
  admit ()

let count_next (#a:eqtype) (x:a) (s:Seq.seq a) (j:nat { j < Seq.length s })
  : Lemma
      (ensures count (Seq.index s j) s (j + 1) == count (Seq.index s j) s j + 1 /\
               (forall (y:a). y =!= Seq.index s j ==> count y s (j + 1) == count y s j)) =
  let s_0_j = Seq.slice s 0 j in
  let sj = Seq.create 1 (Seq.index s j) in
  assert (Seq.equal (Seq.slice s 0 (j + 1)) (Seq.append s_0_j sj));
  Seq.lemma_append_count s_0_j sj

#push-options "--z3rlimit_factor 2"
```pulse
fn majority (#a:eqtype) #p (#s:G.erased _) (votes:array a) (len:SZ.t { SZ.v len == Seq.length s })
  requires pts_to votes #p s ** pure (0 < SZ.v len /\ SZ.fits (2 * SZ.v len))
  returns x:option a
  ensures pts_to votes #p s **
          pure ((x == None ==> (forall (y:a). 2 * count y s (SZ.v len) <= SZ.v len)) /\
                (Some? x ==> SZ.v len < 2 * count (Some?.v x) s (SZ.v len)))
{
  let mut i = 1sz;
  let mut k = 1sz;
  let votes_0 = votes.(0sz);
  let mut cand = votes_0;
  assert (pure (count votes_0 s 1 == 1));
  while (
    let vi = !i;
    (vi <^ len)
  )
  invariant b.
    pts_to votes #p s **
    (exists* vi vk vcand.
       R.pts_to i vi       **
       R.pts_to k vk       **
       R.pts_to cand vcand **
       pure (
         SZ.v vi <= Seq.length s /\
         0 <= SZ.v vk /\ SZ.v vk <= count vcand s (SZ.v vi) /\
         2 * (count vcand s (SZ.v vi) - SZ.v vk) <= SZ.v vi - SZ.v vk /\
         (forall (vcand':a). vcand' =!= vcand ==> 2 * count vcand' s (SZ.v vi) <= SZ.v vi - SZ.v vk) /\
         b == (SZ.v vi < SZ.v len)))
  {
    let vi = !i;
    let vk = !k;
    let vcand = !cand;
    let votes_i = votes.(vi);
    count_next vcand s (SZ.v vi);
    if (vk = 0sz) {
      cand := votes_i;
      k := 1sz;
      i := vi +^ 1sz
    } else if (votes_i = vcand) {
      k := vk +^ 1sz;
      i := vi +^ 1sz
    } else {
      k := vk -^ 1sz;
      i := vi +^ 1sz
    }
  };

  let vk = !k;
  let vcand = !cand;
  if (vk = 0sz) {
    None #a
  } else if (len <^ 2sz *^ vk) {
    Some vcand
  } else {
    i := 0sz;
    k := 0sz;
    while (
      let vi = !i;
      (vi <^ len)
    )
    invariant b.
      pts_to votes #p s **
      (exists* vi vk.
         R.pts_to i vi **
         R.pts_to k vk **
         pure (SZ.v vi <= Seq.length s /\
               SZ.v vk == count vcand s (SZ.v vi) /\
               b == (SZ.v vi < SZ.v len)))
    {
      let vi = !i;
      let vk = !k;
      let votes_i = votes.(vi);
      count_next vcand s (SZ.v vi);
      if (votes_i = vcand) {
        k := vk +^ 1sz;
        i := vi +^ 1sz
      } else {
        i := vi +^ 1sz
      }
    };

    let vk = !k;
    if (len <^ 2sz *^ vk) {
      Some vcand
    } else {
      None #a
    }
  }
}
```
#pop-options
