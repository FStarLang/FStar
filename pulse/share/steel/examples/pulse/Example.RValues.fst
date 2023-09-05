module Example.RValues

open Pulse.Lib.Pervasives
#push-options "--using_facts_from '* -FStar.Tactics -FStar.Reflection' --ext 'pulse:rvalues'"

```pulse
fn test (_:unit)
  requires emp
  returns x:nat
  ensures pure (x == 1)
{
  let mut y = 0;
  y := y + 1;
  y
}
```  
