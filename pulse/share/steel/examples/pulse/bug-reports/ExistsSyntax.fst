module ExistsSyntax
module T = FStar.Tactics
module PM = Pulse.Main
open Steel.ST.Util
open Pulse.Steel.Wrapper
open Steel.ST.Reference
open FStar.Ghost
module U8 = FStar.UInt8
module R = Steel.ST.Reference

[@@expect_failure [228]]
```pulse
fn some_function (r0:ref U8.t) (r1:ref U8.t) (#s:erased U8.t)
   requires (
        R.pts_to r0 full_perm s `star`
        (exists (s1:U8.t). R.pts_to r1 full_perm s1) //this gets parsed as an F* exists prop, rather than a vprop
   )
   ensures (
        emp
   )
{
    let x = !r0;
    let y = !r1;
    admit()
}
```

assume
val some_function (r0:ref U8.t) (r1:ref U8.t) (#s:erased U8.t)
    : stt unit
        (R.pts_to r0 full_perm s `star`
         exists_ (fun (s1:U8.t) -> R.pts_to r1 full_perm s1))
        (fun _ -> emp)

```pulse
fn call_some_function (r0:ref U8.t) (r1:ref U8.t) (#s0:erased U8.t) (#s1:erased U8.t)
   requires (
        R.pts_to r0 full_perm s0 `star`
        R.pts_to r1 full_perm s1
   ) 
   ensures (
        emp
   )
{
    some_function r0 r1;
    ()
}
```
