module UnfoldPure
open Pulse.Steel.Wrapper
module US = FStar.SizeT
module PM = Pulse.Main
open Steel.ST.Util 
open Pulse.Steel.Wrapper


(* no unfold necessary - pulse unfolds pure props automatically? *)

let pre0 (x:nat) : prop = x > 2
let pre1 (x:nat) : prop = pre0 x (* unnecessarily-nested props to test this *)

```pulse
fn unfold_pure1 (#x:nat)
  requires pure (pre1 x)
  ensures pure (x > 1)
{
  ()
}
```


(* unfold necessary - pulse won't automatically unfold a vprop *)

let pre2 (x:nat) : vprop = pure (x > 2)

```pulse
fn unfold_pure2 (#x:nat)
  requires pre2 x
  ensures pure (x > 1)
{
  unfold (pre2 x);
  ()
}
```


(* this breaks - not necessary anyway because the vprop pure(prop)
already puts prop in the context, but a better error message here
(currently just reports "impossible" would be nice *)

[@@expect_failure]
```pulse
fn unfold_pure3 (#x:nat)
  requires pure (x > 2)
  ensures pure (x > 1)
{
  unfold (pure (x > 2));
  ()
}
```