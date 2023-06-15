module ValsInScope
module T = FStar.Tactics
module PM = Pulse.Main
open Steel.ST.Util
open Pulse.Steel.Wrapper

val some_stt_val (_:unit)
    : stt unit emp (fun _ -> emp)

```pulse
fn use_some_stt_val (_:unit)
   requires emp
   ensures emp
{
    some_stt_val()
}
```