module SpinLock
open Pulse.Main
open Pulse.Steel.Wrapper
open FStar.Ghost
open Steel.ST.Util
open Steel.FractionalPermission
module R = Steel.ST.Reference

[@@expect_failure]
```pulse
fn lock_ref (r:R.ref int) (#v_:Ghost.erased int)
  requires R.pts_to r full_perm v_
  ensures emp
{
  let my_lock = new_lock (exists v. R.pts_to r full_perm v);
  ()
}
```

[@@expect_failure]
```pulse
fn create_and_lock_ref (_:unit)
  requires emp
  ensures emp
{
  let mut r = 0;
  let my_lock = new_lock (exists v. R.pts_to r full_perm v);
  ()
}
```