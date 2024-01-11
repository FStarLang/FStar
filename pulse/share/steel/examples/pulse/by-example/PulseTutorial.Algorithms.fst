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

#set-options "--z3rlimit_factor 2"

```pulse
fn read #p (#s:erased _) (arr:array UInt32.t) (len:SZ.t) (i:SZ.t { v len == Seq.length s /\ v i < v len })
  requires pts_to arr #p s
  returns x:UInt32.t
  ensures pts_to arr #p s ** pure (x == Seq.index s (v i))
{
  arr.(i)
}
```

let count_until (#a:eqtype) (x:a) (s:Seq.seq a) (j:nat { j <= Seq.length s }) : GTot nat =
  Seq.count x (Seq.slice s 0 j)

//countlemma$
let count_until_next (#a:eqtype) (x:a) (s:Seq.seq a) (j:nat { j < Seq.length s })
  : Lemma
      (ensures count_until (Seq.index s j) s (j + 1) == count_until (Seq.index s j) s j + 1 /\
               (forall (y:a). y =!= Seq.index s j ==> count_until y s (j + 1) == count_until y s j))
   
//countlemmaend$
  = let s_0_j = Seq.slice s 0 j in
    let sj = Seq.create 1 (Seq.index s j) in
    assert (Seq.equal (Seq.slice s 0 (j + 1)) (Seq.append s_0_j sj));
    Seq.lemma_append_count s_0_j sj

let rec count_len (#a:eqtype) (x:a) (s:Seq.seq a) (j:nat { j <= Seq.length s })
  : Lemma (requires True)
          (ensures count_until x s j <= j)
          (decreases j)
          [SMTPat (count_until x s j)] =
  if j = 0 then ()
  else begin
    count_len x (Seq.slice s 0 (j - 1)) (j - 1);
    count_until_next x s (j - 1)
  end

//majorityspec$
let count (#a:eqtype) (x:a) (s:Seq.seq a) : GTot nat = Seq.count x s

noextract
let has_majority_in (#a:eqtype) (x:a) (s:Seq.seq a) = Seq.length s < 2 * count x s

noextract
let no_majority (#a:eqtype) (s:Seq.seq a) = forall (x:a). ~(x `has_majority_in` s)

```pulse
fn majority (#a:eqtype) #p (#s:G.erased _) (votes:array a) (len:SZ.t { SZ.v len == Seq.length s })
  requires pts_to votes #p s ** pure (0 < SZ.v len /\ SZ.fits (2 * SZ.v len))
  returns x:option a
  ensures pts_to votes #p s **
          pure ((x == None ==> no_majority s) /\ (Some? x ==> (Some?.v x) `has_majority_in` s))
//majorityspecend$
//majorityphase1$
{
  let mut i = 1sz;
  let mut k = 1sz;
  let votes_0 = votes.(0sz);
  let mut cand = votes_0;
  assert (pure (count_until votes_0 s 1 == 1));
  // while loop for phase 1
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
         v vi <= Seq.length s /\
         // v is a spec function that returns nat representation of an FStar.SizeT
         0 <= v vk /\ v vk <= count_until vcand s (v vi) /\
         // constraint for the current candidate,
         2 * (count_until vcand s (v vi) - v vk) <= v vi - v vk /\
         // constraint for the rest of the candidates
         (forall (vcand':a). vcand' =!= vcand ==> 2 * count_until vcand' s (v vi) <= v vi - v vk) /\
         b == (v vi < v len)))
  {
    let vi = !i;
    let vk = !k;
    let vcand = !cand;
    let votes_i = votes.(vi);
    // count_until_next is a lemma that captures the behavior of
    // count when the sequence index is incremented
    count_until_next vcand s (SZ.v vi);
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
  // a couple of optimizations
  if (vk = 0sz) {
    None #a
  } else if (len <^ 2sz *^ vk) {
    Some vcand
  } else {
    i := 0sz;
    k := 0sz;
    // while loop for phase 2
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
               SZ.v vk == count_until vcand s (SZ.v vi) /\
               b == (SZ.v vi < SZ.v len)))
    {
      let vi = !i;
      let vk = !k;
      let votes_i = votes.(vi);
      count_until_next vcand s (SZ.v vi);
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
//majorityphase1end$
```

type u32_t = FStar.UInt32.t

```pulse
//majoritymono$
fn majority_mono #p (#s:G.erased _) (votes:array u32_t) (len:SZ.t { SZ.v len == Seq.length s })
  requires pts_to votes #p s ** pure (0 < SZ.v len /\ SZ.fits (2 * SZ.v len))
  returns x:option u32_t
  ensures pts_to votes #p s **
          pure ((x == None ==> no_majority s) /\ (Some? x ==> (Some?.v x) `has_majority_in` s))
{
  majority #u32_t #p #s votes len
}
//majoritymonoend$
```
