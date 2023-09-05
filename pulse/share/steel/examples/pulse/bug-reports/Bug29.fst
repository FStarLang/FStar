module Bug29
open Pulse.Lib.Pervasives
module U32 = FStar.UInt32
module R = Pulse.Lib.Reference

```pulse
fn test_assert (x y: R.ref int) (#v:erased int)
requires 
    R.pts_to x v **
    R.pts_to y v
ensures
    R.pts_to x v **
    R.pts_to y v 
{
  assert_ (R.pts_to x v);
  ()
}
```


```pulse
fn test_assert2 (x y: R.ref int) (#v:erased int)
requires 
    R.pts_to x v **
    R.pts_to y v
ensures
    R.pts_to x v **
    R.pts_to y v 
{
  assert_ (R.pts_to x v ** R.pts_to y v);
  ()
}
```

[@@expect_failure]
```pulse
fn test_assert_with_duplicates(r: ref nat)
    requires exists v. pts_to r v
    ensures exists v. pts_to r v
{
    with v. assert (pts_to r v ** pts_to r v);
    ()
}
```


```pulse
fn test_with_assert_pure(r: R.ref nat)
    requires R.pts_to r 5 
    ensures R.pts_to r 5
{
    with v. assert (R.pts_to r v ** pure (v = 5));
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