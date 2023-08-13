module ExistsSyntax
open Pulse.Lib.Pervasives
module U8 = FStar.UInt8
module R = Pulse.Lib.Reference

```pulse
fn some_function (r0:ref U8.t) (r1:ref U8.t) (#s:erased U8.t)
   requires 
      R.pts_to r0 s **
      exists (s1:U8.t). R.pts_to r1 s1
   ensures
        emp
{
    let x = !r0;
    let y = !r1;
    admit()
}
```


```pulse
fn call_some_function (r0:ref U8.t) (r1:ref U8.t) (#s0:erased U8.t) (#s1:erased U8.t)
   requires
     R.pts_to r0 s0 **
     R.pts_to r1 s1
   ensures
     emp
{
    some_function r0 r1;
    ()
}
```
