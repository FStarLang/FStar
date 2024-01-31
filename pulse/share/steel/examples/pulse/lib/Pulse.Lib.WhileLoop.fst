module Pulse.Lib.WhileLoop
open Pulse.Main
open Pulse.Lib.Core

```pulse
fn rec while_loop'
  (inv:bool -> vprop)
  (cond:unit -> stt bool (exists* x. inv x) (fun b -> inv b))
  (body:unit -> stt unit (inv true) (fun _ -> exists* x. inv x))
requires (exists* x. inv x) 
ensures inv false
{
  let b = cond ();
  if b
  {
     rewrite (inv b) as (inv true);
     body ();
     while_loop' inv cond body;
  }
  else
  {
    rewrite (inv b) as (inv false);
  }
}
```

let while_loop inv cond body = 
  while_loop' inv (fun _ -> cond) (fun _ -> body)