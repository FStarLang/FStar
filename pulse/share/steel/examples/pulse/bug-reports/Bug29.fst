module Bug29
module T = FStar.Tactics
module PM = Pulse.Main
open Steel.ST.Util 
open Steel.ST.Reference
open Steel.FractionalPermission
open FStar.Ghost
module U32 = FStar.UInt32
open Pulse.Steel.Wrapper
module R = Steel.ST.Reference
#push-options "--ide_id_info_off"

```pulse
fn test_assert (x y: R.ref int) (#v:erased int)
requires 
    R.pts_to x full_perm v **
    R.pts_to y full_perm v
ensures
    R.pts_to x full_perm v **
    R.pts_to y full_perm v 
{
  assert_ (R.pts_to x full_perm v);
  ()
}
```


```pulse
fn test_assert2 (x y: R.ref int) (#v:erased int)
requires 
    R.pts_to x full_perm v **
    R.pts_to y full_perm v
ensures
    R.pts_to x full_perm v **
    R.pts_to y full_perm v 
{
  assert_ (R.pts_to x full_perm v `star` R.pts_to y full_perm v);
  ()
}
```

[@@expect_failure]
```pulse
fn test_assert_with_duplicates(r: ref nat)
    requires exists v. pts_to r full_perm v
    ensures exists v. pts_to r full_perm v
{
    with v. assert (pts_to r full_perm v ** pts_to r full_perm v);
    ()
}
```