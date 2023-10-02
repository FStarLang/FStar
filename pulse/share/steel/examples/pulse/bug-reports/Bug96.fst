module Bug96

open Pulse.Lib.Pervasives

let mini_t = int

```pulse
fn test (z: unit)
  requires emp
  returns y: int
  ensures emp
{
  42;
}
```
```pulse
fn test2 (z: unit)
  requires emp
  returns y: mini_t
  ensures emp
{
  test ()
}
```
