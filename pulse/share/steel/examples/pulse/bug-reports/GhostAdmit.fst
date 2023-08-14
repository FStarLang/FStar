module GhostAdmit
open Pulse.Lib.Pervasives
module A = Pulse.Lib.Array

```pulse
ghost
fn array_pts_to_len (#t:Type0) (a:A.array t) (#p:perm) (#x:Seq.seq t)
    requires A.pts_to a #p x
    ensures A.pts_to a #p x ** pure (A.length a == Seq.length x)
{
    admit()
}
```
