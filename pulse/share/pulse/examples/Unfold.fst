module Unfold

open Pulse.Lib.Pervasives

let unf = ()

assume
val p : slprop

[@@pulse_unfold]
let q = p

```pulse
fn test_pq ()
  requires p
  ensures q
{
  ();
}
```

```pulse
fn test_qp ()
  requires q
  ensures p
{
  ();
}
```
