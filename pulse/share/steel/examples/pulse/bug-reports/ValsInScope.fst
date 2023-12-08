module ValsInScope
open Pulse.Lib.Pervasives

assume
val some_stt_val ()
    : stt unit emp (fun _ -> emp)


```pulse
fn use_some_stt_val ()
   requires emp
   ensures emp
{
    some_stt_val()
}
```

