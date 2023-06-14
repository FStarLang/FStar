module RecordWithRefs
module PM = Pulse.Main
open Steel.ST.Util
open Steel.ST.Reference
open FStar.Ghost
module U8 = FStar.UInt8
module R = Steel.ST.Reference
open Pulse.Steel.Wrapper

noeq
type u8_pair = {
    a: ref U8.t;
    b: ref U8.t
}

let u8_pair_repr = (U8.t & U8.t)

let u8_pair_pred (p:u8_pair) (v:u8_pair_repr) : vprop = 
    R.pts_to p.a full_perm (fst v) `star`
    R.pts_to p.b full_perm (snd v)

[@@expect_failure]
```pulse
fn swap_pair (p: u8_pair) (#v: erased u8_pair_repr)
  requires 
    u8_pair_pred p v
  ensures
    u8_pair_pred p (snd v, fst v)
{
    rewrite (u8_pair_pred p v)
    as      (R.pts_to p.a full_perm (fst v) `star`
             R.pts_to p.b full_perm (snd v));
    let x = !p.a;
    let y = !p.b;
    p.a := y; //p.a doesn't parse on the lhs of an assignemtn
    p.b := x; 
    rewrite (R.pts_to p.a full_perm y `star`
             R.pts_to p.b full_perm x)
        as (u8_pair_pred p (snd v, fst v));
    ()
}
```

```pulse
fn swap_pair (p: u8_pair) (#v: erased u8_pair_repr)
  requires 
    u8_pair_pred p v
  ensures
    u8_pair_pred p (snd v, fst v)
{
    rewrite (u8_pair_pred p v)
    as      (R.pts_to p.a full_perm (fst v) `star`
             R.pts_to p.b full_perm (snd v));
    let x = !p.a;
    let y = !p.b;
    (write p.a y);
    (write p.b x); 
    rewrite (R.pts_to p.a full_perm y `star`
             R.pts_to p.b full_perm x)
        as (u8_pair_pred p (snd v, fst v));
    ()
}
```
