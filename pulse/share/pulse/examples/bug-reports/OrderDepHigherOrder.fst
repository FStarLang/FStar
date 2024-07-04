module OrderDepHigherOrder

open Pulse.Lib.Pervasives
open Pulse.Lib.Mutex

(* A test for order dependency during unification/checking. Flipping or asserting
should not affect the result. *)

assume
val p : int -> slprop
```pulse
fn test (m:mutex int)
  requires mutex_live m p
  ensures  mutex_live m p
{
  let r = lock m;
  unlock m r;
  ()
}
```

```pulse
fn test2 (m:mutex int)
  requires mutex_live m p
  ensures  mutex_live m p
{
  let r = lock m;
  assert (mutex_live m p ** belongs_to r m ** (exists* (x:int). pts_to r x ** p x));
  with x. assert (mutex_live m p ** p x);
  unlock m r;
  ()
}
```


[@@allow_ambiguous]
```pulse
fn flip (#p #q : slprop) (_:unit)
  requires p ** q
  ensures  q ** p
{
  ()
}
```

```pulse
fn test3 (m:mutex int)
  requires mutex_live m p
  ensures  mutex_live m p
{
  let r = lock m;
  flip ();
  unlock m r;
  ()
}
```

