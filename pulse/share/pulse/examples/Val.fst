module Val

open Pulse.Lib.Pervasives

```pulse
fn foo ()
  requires emp
  ensures emp
{
  ()
}
```

let x = foo()
