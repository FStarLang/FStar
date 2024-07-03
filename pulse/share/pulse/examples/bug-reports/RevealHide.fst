module RevealHide

open Pulse.Lib.Pervasives

assume val p : int -> slprop

```pulse
fn test0 (x:int)
  requires p x
  ensures  p (reveal (hide x))
{
  ()
}
```

```pulse
fn test1 (x:int)
  requires p (reveal (hide x))
  ensures  p x
{
  ()
}
```
