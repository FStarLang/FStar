module Match

#lang-pulse
open Pulse

type abc = | A

fn foo (r : ref abc) (#zzz : erased abc)
  preserves r |-> zzz
{
  let z = !r;
  match z {
    A -> {
     (* The branch's rewrites_to hypothesis supplies the substitution. *)
     ()
   }
  };
}
