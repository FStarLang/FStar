module Bug.SpinLock
open Pulse.Lib.Pervasives
module R = Pulse.Lib.Reference
open Pulse.Lib.SpinLock

let test_fstar (r:R.ref int) =
  let my_lock = new_lock (exists* v. R.pts_to r v) in
  ()

```pulse
fn lock_ref (r:R.ref int) (#v_:Ghost.erased int)
  requires R.pts_to r v_
  ensures emp
{
  let my_lock = new_lock (exists* v. R.pts_to r v);
  ()
}
```

[@@expect_failure]
```pulse
fn create_and_lock_ref ()
  requires emp
  ensures emp
{
  let mut r = 0;
  let my_lock = new_lock (exists* v. R.pts_to r v);
  ()
}
```