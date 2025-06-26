module Test.ReflikeClass
#lang-pulse

open FStar.Tactics.Typeclasses
open Pulse.Lib.Pervasives
module Box = Pulse.Lib.Box

[@@fundeps [0]; pulse_unfold]
class reflike (vt:Type) (rt:Type) = {
  ( |-> ) : rt -> vt -> slprop;
  alloc   : v:vt -> stt rt emp (fun r -> r |-> v);
  (!) : r:rt -> #v0:erased vt -> stt vt (r |-> v0) (fun v -> (r |-> v0) ** pure (Ghost.reveal v0 == v));
  (:=) : r:rt -> v:vt -> #v0:erased vt -> stt unit (r |-> v0) (fun _ -> r |-> v);
}

(* Prevent warning about using alloc... this is just a test. *)
#push-options "--warn_error -288"
instance reflike_ref (a:Type) : reflike a (ref a) = {
  ( |-> ) = (fun r v -> Pulse.Lib.Reference.pts_to r v);
  alloc   = Pulse.Lib.Reference.alloc;
  ( ! )   = (fun r #v0 -> Pulse.Lib.Reference.op_Bang r #v0 #1.0R);
  ( := )  = (fun r v #v0 -> Pulse.Lib.Reference.op_Colon_Equals r v #v0);
}
#pop-options

instance reflike_box (a:Type) : reflike a (Box.box a) = {
  ( |-> ) = (fun r v -> Pulse.Lib.Box.pts_to r v);
  alloc   = Pulse.Lib.Box.alloc;
  ( ! )   = (fun r #v0 -> Pulse.Lib.Box.op_Bang r #v0 #1.0R);
  ( := )  = (fun r v #v0 -> Pulse.Lib.Box.op_Colon_Equals r v #v0);
}


fn test1 (r : ref int)
  requires r |-> 1
  ensures  r |-> 2
{
  let x = !r;
  assert (pure (x == 1));
  r := 2;
  let y = !r;
  assert (pure (y == 2));
  ()
}



fn test2 (r : Box.box int)
  requires r |-> 1
  ensures  r |-> 2
{
  let x = !r;
  assert (pure (x == 1));
  r := 2;
  let y = !r;
  assert (pure (y == 2));
  ()
}

