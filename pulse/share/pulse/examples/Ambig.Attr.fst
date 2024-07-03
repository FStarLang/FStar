module Ambig.Attr

open Pulse.Lib.Pervasives

assume val p : int -> slprop

[@@allow_ambiguous]
assume val foo () (#x:erased int)
  : stt unit (p x) (fun _ -> emp)

(* unlucky *)
[@@expect_failure]
```pulse
fn ambig1 ()
  requires p 1 ** p 2
  ensures p 1
{
  foo ();
  ()
}
```

(* lucky *)
```pulse
fn ambig2 ()
  requires p 1 ** p 2
  ensures p 2
{
  foo ();
  ()
}
```

```pulse
fn ambig ()
  requires p 1 ** p 2
  ensures emp
{
  foo ();
  foo ();
  ()
}
```
