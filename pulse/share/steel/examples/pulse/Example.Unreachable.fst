module Example.Unreachable
open Pulse.Lib.Pervasives


```pulse
fn test (x:option bool)
    requires pure (Some? x)
    returns b:bool 
    ensures emp
{
    match x {
     Some b -> { b }
     None -> { unreachable () }
    }
}
```
