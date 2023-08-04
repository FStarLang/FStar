module Bug29
open Pulse.Lib.Pervasives
module U32 = FStar.UInt32
module R = Pulse.Lib.Reference

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
  assert_ (R.pts_to x full_perm v ** R.pts_to y full_perm v);
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


```pulse
fn test_with_assert_pure(r: R.ref nat)
    requires R.pts_to r full_perm 5 
    ensures R.pts_to r full_perm 5
{
    with v. assert (R.pts_to r full_perm v ** pure (v = 5));
    ()
}
```

```pulse
fn trivial (x:unit)
requires emp
ensures emp
{
  assert (pure (5 == 5));
  ()
}
```