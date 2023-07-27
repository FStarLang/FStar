module GhostAdmit
module T = FStar.Tactics
module PM = Pulse.Main
open Steel.ST.Util
open Steel.FractionalPermission
open FStar.Ghost
module A = Steel.ST.Array
open Pulse.Steel.Wrapper
// Note, writing it this way fails. Can't admit in ghost?? 

[@@expect_failure]
```pulse
ghost
fn array_pts_to_len (#t:Type0) (a:A.array t) (#p:perm) (#x:Seq.seq t)
    requires A.pts_to a p x
    ensures A.pts_to a p x ** pure (A.length a == Seq.length x)
{
    admit()
}
```
