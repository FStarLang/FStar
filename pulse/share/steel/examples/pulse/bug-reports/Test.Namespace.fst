module Test.Namespace
open Pulse.Steel.Wrapper
open Pulse.Main
open Steel.ST.Util

```pulse
fn test (_:unit)
   requires emp
   ensures emp
{
    ()
}
```