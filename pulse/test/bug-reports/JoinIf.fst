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

module JoinIf
#lang-pulse
open Pulse.Lib.Pervasives
module U32 = FStar.UInt32
module A = Pulse.Lib.Array
module R = Pulse.Lib.Reference
open FStar.UInt32

let sorted (s0 s:Seq.seq U32.t) =
   (forall (i:nat). i < Seq.length s - 1 ==> U32.v (Seq.index s i) <= U32.v (Seq.index s (i + 1))) /\
   (forall (i:nat). i < Seq.length s0 ==> (exists (j:nat). j < Seq.length s /\ U32.v (Seq.index s0 i) == U32.v (Seq.index s j)))

fn sort3_alt (a:array U32.t)
             (x y z: ref U32.t)
             (#s:(s:Ghost.erased (Seq.seq U32.t) {Seq.length s == 3}))
   requires (A.pts_to a s)
   ensures 
      exists* s'. (
         A.pts_to a s' **
         pure (sorted s s')
      )
{
   let mut x = a.(0sz);
   let mut y = a.(1sz);
   let mut z = a.(2sz);
   let vx = !x;
   let vy = !y;
   if (vy <^ vx)
   {
      x := vy;
      y := vx;
   };
   let vx = !x;
   let vz = !z;
   if (vz <^ vx)
   {
      x := vz;
      z := vx;
   };
   let vy = !y;
   let vz = !z;
   if (vz <^ vy)
   {
      y := vz;
      z := vy;
   };
   (a.(0sz) <- !x);
   (a.(1sz) <- !y);
   (a.(2sz) <- !z);
}


//An explicitly annotated version works too, but is very verbose
fn sort3_alt2 (a:array U32.t)
              (#s:(s:Ghost.erased (Seq.seq U32.t) {Seq.length s == 3}))
   requires (A.pts_to a s)
   ensures 
      exists* s'. (
         A.pts_to a s' **
         pure (sorted s s')
      )
{
   let mut x = a.(0sz);
   let mut y = a.(1sz);
   let mut z = a.(2sz);
   let vx0 = !x;
   let vy0 = !y;
   if (vy0 <^ vx0)
   ensures (
    R.pts_to x (if vy0 <^ vx0 then vy0 else vx0) **
    R.pts_to y (if vy0 <^ vx0 then vx0 else vy0) **
    A.pts_to a s **
    (z |-> Seq.index s 2)
   )
   {
      x := vy0;
      y := vx0;
   };
   let vx1 = !x;
   let vz1 = !z;
   if (vz1 <^ vx1)
   ensures (
    R.pts_to x (if vz1 <^ vx1 then vz1 else vx1) **
    R.pts_to y (if vy0 <^ vx0 then vx0 else vy0) **
    R.pts_to z (if vz1 <^ vx1 then vx1 else vz1) **
    A.pts_to a s
   )
   {
      x := vz1;
      z := vx1;
   };
   let vy2 = !y;
   let vz2 = !z;
   if (vz2 <^ vy2)
   ensures (
    R.pts_to x (if vz1 <^ vx1 then vz1 else vx1) **
    R.pts_to y (if vz2 <^ vy2 then vz2 else vy2) **
    R.pts_to z (if vz2 <^ vy2 then vy2 else vz2) **
    A.pts_to a s
   )
   {
      y := vz2;
      z := vy2;
   };
   (a.(0sz) <- !x);
   (a.(1sz) <- !y);
   (a.(2sz) <- !z);
}
