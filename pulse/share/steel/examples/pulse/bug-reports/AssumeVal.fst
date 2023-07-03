module AssumeVal
module PM = Pulse.Main
open Steel.ST.Util 
open Pulse.Steel.Wrapper
module U8 = FStar.UInt8

val v0 : int
let v1 : int = 0
assume val v2 : int

// Pulse allows us to reference v0 even though it is not assumed
```pulse
fn use (_:U8.t)
  requires emp
  ensures emp
{
  let v = v0 + v1 + v2;
  ()
}
```