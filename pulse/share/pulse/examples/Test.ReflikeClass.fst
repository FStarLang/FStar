module Test.ReflikeClass

open FStar.Tactics.Typeclasses
open Pulse.Lib.Pervasives

[@@fundeps [0]]
class reflike (vt:Type) (rt:Type) = {
  ( |-> ) : rt -> vt -> slprop;
  alloc   : v:vt -> stt rt emp (fun r -> r |-> v);
  read    : r:rt -> #v0:erased vt ->
            stt vt (r |-> v0) (fun v -> (r |-> v0) ** pure (Ghost.reveal v0 == v));
}

instance reflike_ref (a:Type) : reflike a (ref a) = {
  ( |-> ) = (fun r v -> Pulse.Lib.Reference.pts_to r v);
  alloc   = Pulse.Lib.Reference.alloc;
  read    = (fun r #v0 -> Pulse.Lib.Reference.op_Bang r #v0 #1.0R);
}

```pulse
fn test1 (r : ref int)
  requires r |-> 1
  ensures  r |-> 1
{
  (* Akward rewrites... We need to unfold the methods and dictionaries eagerly. *)
  rewrite (r |-> 1) as (reflike_ref int).op_Bar_Subtraction_Greater r 1;
  let x = read r;
  rewrite (reflike_ref int).op_Bar_Subtraction_Greater r 1 as (r |-> 1);
  assert (pure (x == 1));
  ()
}
```
