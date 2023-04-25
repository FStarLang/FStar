module CustomSyntax
open Pulse.Steel.Wrapper

```pulse
fun (x:true)
  requires true
  ensures r. false ->
   return false
```
