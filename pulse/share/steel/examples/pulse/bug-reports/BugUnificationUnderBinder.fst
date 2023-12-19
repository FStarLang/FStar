module BugUnificationUnderBinder
open Pulse.Lib.Pervasives

assume
val p (x:int) (y:int) : vprop

```pulse
fn test (_:unit)
requires exists* x. p x 5
ensures emp
{
    with zz. assert (exists* x. p x zz);
    drop_ _;
}
```

```pulse
fn test_fa (_:unit)
requires forall* x. p x 5
ensures emp
{
    with zz. assert (forall* x. p x zz);
    drop_ _;
}
```
