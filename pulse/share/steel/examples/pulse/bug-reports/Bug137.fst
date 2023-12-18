module Bug137

open Pulse.Lib.Pervasives

```pulse
fn test_elim_pure (x:option bool)
requires exists* q. q ** pure (Some? x)
ensures exists* q. q ** pure (Some? x)
{
    let v = Some?.v x;
    ()
}
```

```pulse
fn test_elim_pure2 (x:option bool)
requires exists* p q. p ** (exists* r. r ** pure (Some? x)) ** q
ensures exists* p q. p ** q ** (exists* r. r ** pure (Some? x))
{
    let v = Some?.v x;
    ()
}
```
