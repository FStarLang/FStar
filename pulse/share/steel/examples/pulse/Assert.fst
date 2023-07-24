module Assert
module PM = Pulse.Main
open Steel.ST.Util 
open Steel.ST.Reference
open Steel.FractionalPermission
open FStar.Ghost
open Pulse.Steel.Wrapper

```pulse
fn test_assert (r0 r1: ref nat)
               (#p0 #p1:perm)
               (#v0:nat)
    requires 
        pts_to r0 p0 v0 **
        (exists v1. pts_to r1 p1 v1)
    ensures
        pts_to r0 p0 v0 **
        (exists v1. pts_to r1 p1 v1)
{
    //assert_ (pts_to r1 ?p1 ?v1); would be nice to have a version that also binds witnesses
    assert_ (pts_to r0 p0 (v0 + 0));
    ()
}
```
