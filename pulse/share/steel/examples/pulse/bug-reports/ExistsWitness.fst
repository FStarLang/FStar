module ExistsWitness
module PM = Pulse.Main
open Steel.ST.Util
open Steel.ST.Reference
open FStar.Ghost
module U8 = FStar.UInt8
module R = Steel.ST.Reference
open Pulse.Steel.Wrapper
//This example illustrates how to get your "hands" on an existential witness
//Using the `with ... assert` construct

```pulse
fn get_witness (x:R.ref int) (#p:perm) (#y:Ghost.erased int)
requires R.pts_to x p y
returns z:Ghost.erased int
ensures R.pts_to x p y ** pure (y==z)
{   
    y
}
```

let assume_squash (p:prop) : squash p = assume p

//This fails because as it opens the existential for `p`
//it adds an extra level of reveal/hide around it
//and this causes the match to fail; although one would expect
//F* to cancel the additional layer of reveal/hide
[@@expect_failure]    
```pulse
fn sample (x:R.ref int)
requires exists p y. R.pts_to x p y
ensures exists p y. R.pts_to x p y ** pure (y == 17)
{
    let y' = get_witness x;
    assume_squash (y'==17);
    ()
}
```

```pulse
fn sample_ (x:R.ref int) (#p:perm)
requires exists y. R.pts_to x p y
ensures exists y. R.pts_to x p y ** pure (y == 17)
{
    let y = get_witness x;
    assume_squash (y==17);
    ()
}
```

```pulse
fn sample2 (x:R.ref int) (#p:perm)
requires exists y. R.pts_to x p y
ensures exists y. R.pts_to x p y ** pure (y == 17)
{
    with (y:erased _).
    assert (R.pts_to x p y);
    assume_squash (y==17);
    ()
}
```

assume val drop (p:vprop) : stt unit p (fun _ -> emp)

```pulse
fn sample3 (x0:R.ref int) (x1:R.ref bool) (#p0 #p1:perm)
requires exists v0 v1. R.pts_to x0 p0 v0 ** R.pts_to x1 p1 v1
ensures emp
{
    
    with (v0 v1:erased _).
    assert (R.pts_to x0 p0 v0 ** R.pts_to x1 p1 v1);
    drop (R.pts_to x0 p0 v0);
    drop (R.pts_to x1 p1 v1);
    ()
}
```

```pulse
fn sample4 (x0:R.ref int) (x1:R.ref bool) (#p0 #p1:perm)
requires exists v0 v1. R.pts_to x0 p0 v0 ** R.pts_to x1 p1 v1
ensures emp
{
    
    with v0 v1.
    assert R.pts_to x0 p0 v0 ** R.pts_to x1 p1 v1;
    drop (R.pts_to x0 p0 v0);
    drop (R.pts_to x1 p1 v1);
    ()
}
```

```pulse
fn sample5 (x0:R.ref int) (x1:R.ref bool) (#p0 #p1:perm)
requires exists v0 v1. R.pts_to x0 p0 v0 ** R.pts_to x1 p1 v1
ensures emp
{
    
    with v0.
    assert R.pts_to x0 p0 v0;
    with v1.
    assert R.pts_to x1 p1 v1;
    drop (R.pts_to x0 p0 v0);
    drop (R.pts_to x1 p1 v1);
    ()
}
```

```pulse
fn sample6 (x0:R.ref int) (x1:R.ref bool)
requires exists p0 p1 v0 v1. R.pts_to x0 p0 v0 ** R.pts_to x1 p1 v1
ensures emp
{
    
    with p0 p1 v0 v1.
    assert R.pts_to x0 p0 v0 ** R.pts_to x1 p1 v1;
    drop (R.pts_to x0 p0 v0);
    drop (R.pts_to x1 p1 v1);
    ()
}
```