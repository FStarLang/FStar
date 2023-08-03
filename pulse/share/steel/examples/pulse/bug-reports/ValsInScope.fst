module ValsInScope
open Pulse.Lib.Pervasives

assume
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

