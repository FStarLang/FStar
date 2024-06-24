module Test.RewriteBy

open Pulse.Lib.Pervasives
open FStar.Tactics.V2

assume val p : vprop
assume val q : vprop

let tac () : Tac unit =
   dump "test";
   tadmit ()

```pulse
fn test1 ()
  requires p
  ensures  q
{
  rewrite p
       as q
       by tadmit ();
}
```

(* lambdas are broken, looks like F* bug? *)
[@@expect_failure]
```pulse
fn test ()
  requires p
  ensures  q
{
  rewrite p
       as q
       by (
         dump "a";
         tac ()
       );
}
```

let dump_trefl (s:string) : Tac unit =
  dump s;
  vprop_equiv_norm ()

```pulse
fn test ()
  requires p
  ensures  p
{
  rewrite p
       as p
       by dump_trefl "test";
}
```
