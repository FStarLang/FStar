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

module Pulse.Lib.Vec

open Pulse.Lib.Core
open Pulse.Lib.Pervasives

module R = Pulse.Lib.Reference
module A = Pulse.Lib.Array.Core

type vec a = A.array a
let length v = A.length v
let is_full_vec v = A.is_full_array v
let pts_to v #p s = A.pts_to v #p s
let pts_to_is_small _ _ _ = ()
let pts_to_len v = A.pts_to_len v
let alloc x n = A.alloc x n
let op_Array_Access v i #p #s = A.op_Array_Access v i #p #s
let op_Array_Assignment v i x #s = A.op_Array_Assignment v i x #s
let free v #s = A.free v #s
let share v = A.share v
let gather v = A.gather v

let vec_to_array v = v
let to_array_pts_to v #p #s =
  rewrite (pts_to v #p s)
          (A.pts_to (vec_to_array v) #p s)
          (vprop_equiv_refl _)
let to_vec_pts_to v #p #s =
  rewrite (A.pts_to (vec_to_array v) #p s)
          (pts_to v #p s)
          (vprop_equiv_refl _)

```pulse
fn read_ref' (#a:Type0) (r:R.ref (vec a)) (i:SZ.t)
  (#v:erased (vec a))
  (#s:(s:erased (Seq.seq a) { SZ.v i < Seq.length s }))
  requires R.pts_to r v ** pts_to v s
  returns x:a
  ensures R.pts_to r v ** pts_to v s ** pure (x == Seq.index s (SZ.v i))
{
  let vc = !r;
  rewrite (pts_to (reveal v) s)
       as (pts_to vc s);
  let x = op_Array_Access vc i;
  rewrite (pts_to vc s)
       as (pts_to (reveal v) s);
  x
}
```

let read_ref = read_ref'

```pulse
fn write_ref' (#a:Type0) (r:R.ref (vec a)) (i:SZ.t) (x:a)
  (#v:erased (vec a))
  (#s:(s:erased (Seq.seq a) { SZ.v i < Seq.length s }))
  requires R.pts_to r v ** pts_to v s
  ensures R.pts_to r v ** pts_to v (Seq.upd s (SZ.v i) x)
{
  let vc = !r;
  rewrite (pts_to (reveal v) s)
       as (pts_to vc s);
  op_Array_Assignment vc i x;
  with s. assert (pts_to vc s);
  rewrite (pts_to vc s)
       as (pts_to (reveal v) s)
}
```

let write_ref = write_ref'

```pulse
fn replace_i' (#a:Type0) (v:vec a) (i:SZ.t) (x:a)
  (#s:(s:erased (Seq.seq a) { SZ.v i < Seq.length s }))
  requires pts_to v s
  returns res:a
  ensures pts_to v (Seq.upd s (SZ.v i) x) ** pure (res == Seq.index s (SZ.v i))
{
  let y = op_Array_Access v i;
  op_Array_Assignment v i x;
  y
}
```

let replace_i = replace_i'

```pulse
fn replace_i_ref' (#a:Type0) (r:R.ref (vec a)) (i:SZ.t) (x:a)
  (#v:erased (vec a))
  (#s:erased (Seq.seq a) { SZ.v i < Seq.length s })
  requires R.pts_to r v ** pts_to v s
  returns res:a
  ensures R.pts_to r v ** pts_to v (Seq.upd s (SZ.v i) x) ** pure (res == Seq.index s (SZ.v i))
{
  let vc = !r;
  rewrite (pts_to v s)
       as (pts_to vc s);
  let y = op_Array_Access vc i;
  op_Array_Assignment vc i x;
  with #s. assert (pts_to vc s);
  rewrite (pts_to vc s)
       as (pts_to v s);
  y
}
```

let replace_i_ref = replace_i_ref'
