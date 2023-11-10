module GhostSeq

open Pulse.Lib.Pervasives

```pulse
ghost
fn basic_ghost (_:unit)
  requires emp
  ensures emp
{
  (); ()
}
```
