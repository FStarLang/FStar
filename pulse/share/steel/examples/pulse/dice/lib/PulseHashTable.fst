module PulseHashTable
module PM = Pulse.Main
open Steel.ST.Array
open Steel.FractionalPermission
open Steel.ST.Util
open FStar.Ghost
open Pulse.Steel.Wrapper
module A = Steel.ST.Array
module R = Steel.ST.Reference
module US = FStar.SizeT
module U8 = FStar.UInt8
module LK = Steel.ST.SpinLock
module PHT = LinearScanHashTable
open LinearScanHashTable

noeq
type ht (s : pht_sig) = {
  sz : pos;
  contents : A.larray (cell s.keyt s.valt) sz;
}

let models (s:pht_sig) (pht:pht s) (ht:ht s) : vprop
= A.pts_to ht.contents full_perm pht.repr `star`
  pure (pht.sz == ht.sz)

```pulse
fn insert (#s:pht_sig) (#pht:(p:pht s{not_full p.repr})) 
          (table:ht s) (k:s.keyt) (v:s.valt)
  requires models s pht table
  ensures  models s (PHT.insert pht k v) table
{
  admit()
}
```

```pulse
fn delete (#s:pht_sig) (#pht:(p:pht s{not_full p.repr})) 
          (table:ht s) (k:s.keyt)
  requires models s pht table
  ensures  models s (PHT.delete pht k) table
{
  admit()
}
```

```pulse
fn lookup (#s:pht_sig) (#pht:(p:pht s{not_full p.repr})) 
          (table:ht s) (k:s.keyt)
  requires models s pht table
  returns  o:option s.valt
  ensures  models s pht table
{
  admit()
}
```