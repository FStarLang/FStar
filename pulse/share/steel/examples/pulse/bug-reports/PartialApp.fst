module PartialApp
open Pulse.Lib.Pervasives

```pulse
fn my_fn (#t:Type0) (x y:t) 
  requires emp
  ensures emp
{
  ()
}
```

// Line 22 is a partial application that returns _:t -> unit.
// We should warn the user in case this return type was unintentional. 
```pulse
fn app (#t:Type0) (v:t)
  requires emp
  ensures emp
{
  my_fn v;
  my_fn v v;
  ()
}
```