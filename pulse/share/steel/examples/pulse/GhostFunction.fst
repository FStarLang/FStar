module GhostFunction
module PM = Pulse.Main
open Steel.ST.Util
open Steel.ST.Reference
open FStar.Ghost
module U8 = FStar.UInt8
module R = Steel.ST.Reference
open Pulse.Steel.Wrapper
module GR = Steel.ST.GhostReference

[@@expect_failure]
```pulse
fn increment (x:GR.ref int) (#n:erased int)
    requires GR.pts_to x full_perm n
    ensures GR.pts_to x full_perm (n + 1)
{
   let v = gread x;
   gwrite x (v + 1)
}
```

```pulse
ghost
fn increment (x:GR.ref int) (#n:erased int)
    requires GR.pts_to x full_perm n
    ensures GR.pts_to x full_perm (n + 1)
{
   let v = gread x;
   gwrite x (v + 1)
}
```