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

module Pulse.Lib.Array
module PM = Pulse.Main
open Pulse.Lib.Core
open Pulse.Lib.Reference
open Pulse.Lib.Array.Core
open FStar.Ghost
module US = FStar.SizeT
module U8 = FStar.UInt8
open Pulse.Lib.BoundedIntegers
module A = Pulse.Lib.Array.Core
module R = Pulse.Lib.Reference

#set-options "--print_implicits"
```pulse
fn compare (#t:eqtype) (l:US.t) (a1 a2:larray t (US.v l)) (#p1 #p2:perm)
  requires pts_to a1 #p1 's1
        ** pts_to a2 #p2 's2
  returns res:bool
  ensures pts_to a1 #p1 's1
       ** pts_to a2 #p2 's2
       ** (pure (res <==> Seq.equal 's1 's2))
{
  pts_to_len a1 #p1 #'s1;
  pts_to_len a2 #p2 #'s2;
  let mut i = 0sz;
  while (let vi = !i; 
    if (vi < l) { 
      let v1 = a1.(vi); 
      let v2 = a2.(vi); 
      (v1 = v2) } 
    else { false } )
  invariant b. exists* (vi:US.t). ( 
    R.pts_to i vi **
    A.pts_to a1 #p1 's1 **
    A.pts_to a2 #p2 's2 **
    pure (vi <= l
       /\ (b == (vi < l && Seq.index 's1 (US.v vi) = Seq.index 's2 (US.v vi)))
       /\ (forall (i:nat). i < US.v vi ==> Seq.index 's1 i == Seq.index 's2 i)))
  {
    let vi = !i; 
    i := vi + 1sz;
  };
  let vi = !i;
  let res = vi = l;
  res
}
```

```pulse 
fn memcpy_l (#t:eqtype) (l:US.t) (src dst:(a:array t { US.v l <= A.length a }))
           (#p:perm) (#src0 #dst0:Ghost.erased (Seq.seq t))
  requires A.pts_to src #p src0 **
           A.pts_to dst dst0
  returns _:squash (Seq.length src0 == A.length src /\ Seq.length dst0 == A.length dst)
  ensures A.pts_to src #p src0 **
          A.pts_to dst (Seq.append (Seq.slice src0 0 (US.v l))
                                   (Seq.slice dst0 (US.v l) (A.length dst)))
{
  pts_to_len src #p #src0;
  pts_to_len dst #1.0R #dst0;
  let mut i = 0sz;
  while (let vi = !i; (vi < l) )
  invariant b. exists* (vi:US.t) (s:Seq.seq t). ( 
    R.pts_to i vi **
    A.pts_to src #p src0 **
    A.pts_to dst s **
    pure (vi <= l
       /\ Seq.length s == Seq.length dst0
       /\ (b == (vi < l))
       /\ (forall (i:nat). i < US.v vi ==> Seq.index src0 i == Seq.index s i)
       /\ (forall (i:nat). (US.v vi <= i /\ i < Seq.length s) ==> Seq.index s i == Seq.index dst0 i)))

  {
    let vi = !i;
    let x = src.(vi);
    with s. assert (A.pts_to dst s);
    (dst.(vi) <- x);
    i := vi + 1sz;
  };
  with s. assert (A.pts_to dst s);
  assert_ (pure (Seq.equal s (Seq.append (Seq.slice src0 0 (US.v l))
                                         (Seq.slice dst0 (US.v l) (A.length dst)))));
  ()
}
```

```pulse
fn memcpy
  (#t:eqtype)
  (l:SZ.t)
  (src dst:larray t (SZ.v l))
  (#p:perm)
  (#src0 #dst0:Ghost.erased (Seq.seq t))
  requires pts_to src #p src0 **
           pts_to dst dst0
  ensures pts_to src #p src0 **
          pts_to dst src0
{
  memcpy_l l src dst;
  with s. assert (A.pts_to dst s);
  assert_ (pure (Seq.equal s src0));
  ()
}
```

```pulse
fn fill (#t:Type0) (l:US.t) (a:larray t (US.v l)) (v:t)
  requires A.pts_to a 's
  ensures exists* (s:Seq.seq t).
    A.pts_to a s **
    pure (s `Seq.equal` Seq.create (US.v l) v)
{
  pts_to_len a #1.0R #'s;
  let mut i = 0sz;
  while (let vi = !i; (vi < l))
  invariant b. exists* (vi:US.t) (s:Seq.seq t). ( 
    R.pts_to i vi **
    A.pts_to a s **
    pure (vi <= l
        /\ Seq.length s == US.v l
        /\ (b == (vi < l))
        /\ (forall (i:nat). i < US.v vi ==> Seq.index s i == v)))
  {
    let vi = !i; 
    (a.(vi) <- v);
    i := vi + 1sz;
  }
}
```

```pulse
fn zeroize (l:US.t) (a:larray U8.t (US.v l))
  requires A.pts_to a 's
  ensures exists* (s:Seq.seq U8.t).
    A.pts_to a s **
    pure (s `Seq.equal` Seq.create (US.v l) 0uy)
{
  pts_to_len a #1.0R #'s;
  fill l a 0uy
}
```
