module Bug102

open Pulse.Lib.Pervasives

assume val p : vprop

let rec foo (x:nat) : vprop =
  if x = 0 then
    emp
  else
    p ** foo (x-1)

```pulse
fn test_unfold ()
  requires foo 2
  ensures  p ** foo 1
{
  unfold foo 2;
}
```

```pulse
fn test_fold ()
  requires p ** foo 1
  ensures  foo 2
{
  fold foo 2;
}
```
