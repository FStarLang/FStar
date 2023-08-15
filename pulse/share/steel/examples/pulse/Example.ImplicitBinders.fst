module Example.ImplicitBinders
open Pulse.Lib.Pervasives
module U32 = FStar.UInt32
#push-options "--using_facts_from '* -FStar.Tactics -FStar.Reflection'"



```pulse
fn swap (r1 r2:ref U32.t)
  requires 
      pts_to r1 'n1 **
      pts_to r2 'n2
  ensures
      pts_to r1 'n2 **
      pts_to r2 'n1
{
  let x = !r1;
  let y = !r2;
  r1 := y;
  r2 := x
}
```

```pulse
fn test_read (r:ref U32.t)
   requires pts_to r #p 'n
   returns x : U32.t
   ensures pts_to r #p x
{
  !r
}
```