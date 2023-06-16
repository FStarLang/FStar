module ExistsWitness
module PM = Pulse.Main
open Steel.ST.Util
open Steel.ST.Reference
open FStar.Ghost
module U8 = FStar.UInt8
module R = Steel.ST.Reference
open Pulse.Steel.Wrapper
//This example illustrates how to get your "hands" on an existential witness
//But, it is also very specific; is there a generic way to do this?

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
    let y = get_witness x;
    assume_squash (y==17);
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