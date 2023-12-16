module Pulse.Lib.HashTable.Type

open Pulse.Lib.Pervasives
module V = Pulse.Lib.Vec
module R = Pulse.Lib.Reference
module SZ = FStar.SizeT

let token (#k:eqtype) (#v:Type0)
  (r:ref (ht_t k v))
  (r_sz:ref pos_us)
  (r_hashf:ref (k -> SZ.t))
  (r_contents:ref (V.vec (cell k v))) : vprop =
  exists* ht. pts_to r ht


```pulse
fn explode_ref_ht_t' (#k:eqtype) (#v:Type0) (#ht:erased (ht_t k v)) (r:ref (ht_t k v))
  requires pts_to r ht
  returns res:(ref pos_us & ref (k -> SZ.t) & ref (V.vec (cell k v)))
  ensures exploded_vp r ht (tfst res) (tsnd res) (tthd res)
{
  let htc = !r;
  let r_sz = R.alloc htc.sz;
  let r_hashf = R.alloc htc.hashf;
  let r_contents = R.alloc htc.contents;
  let res = (r_sz, r_hashf, r_contents);
  fold (token r r_sz r_hashf r_contents);
  fold (exploded_vp r ht r_sz r_hashf r_contents);
  rewrite (exploded_vp r ht r_sz r_hashf r_contents)
       as (exploded_vp r ht (tfst res) (tsnd res) (tthd res));
  res
}
```

let explode_ref_ht_t = explode_ref_ht_t'

```pulse
fn unexplode_ref' (#k:eqtype) (#v:Type0) (#ht:erased (ht_t k v))
  (r:ref (ht_t k v))
  (r_sz:ref pos_us)
  (r_hashf:ref (k -> SZ.t))
  (r_contents:ref (V.vec (cell k v)))
  requires exploded_vp r ht r_sz r_hashf r_contents
  ensures pts_to r ht
{
  unfold (exploded_vp r ht r_sz r_hashf r_contents);
  unfold (token r r_sz r_hashf r_contents);
  let sz = !r_sz;
  let hashf = !r_hashf;
  let contents = !r_contents;
  free r_sz; free r_hashf; free r_contents;
  let s = {sz; hashf; contents};
  r := s
}
```

let unexplode_ref = unexplode_ref'
