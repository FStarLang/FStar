module Pulse.Lib.Vec

open Pulse.Lib.Core
open Pulse.Lib.Pervasives

module R = Pulse.Lib.Reference
module A = Pulse.Lib.Array.Core

type vec a = A.array a
let length v = A.length v
let is_full_vec v = A.is_full_array v
let pts_to v #p s = A.pts_to v #p s
let pts_to_len v = A.pts_to_len v
let alloc x n = A.alloc x n
let op_Array_Access v i = A.op_Array_Access v i
let op_Array_Assignment v i x = A.op_Array_Assignment v i x
let free v = A.free v

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
fn vec_ref_read' (#a:Type0) (r:R.ref (vec a)) (i:SZ.t)
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

let vec_ref_read = vec_ref_read'

```pulse
fn vec_ref_write' (#a:Type0) (r:R.ref (vec a)) (i:SZ.t) (x:a)
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

let vec_ref_write = vec_ref_write'
