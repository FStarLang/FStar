module Test.Namespace
open Pulse.Steel.Wrapper
open Pulse.Main
open Steel.ST.Util

(* uncomment this to see the failure
```pulse
fn test (_:unit)
   requires emp
   ensures emp
{
    ()
}
```
*)