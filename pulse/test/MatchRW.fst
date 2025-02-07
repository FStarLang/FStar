module MatchRW
#lang-pulse

open Pulse.Lib.Pervasives

assume
val p ([@@@equate_strict] b : bool) : slprop

assume
val q : slprop

assume
val foo1 () : stt_ghost unit [] (p true) (fun _ -> q)

assume
val foo2 () : stt_ghost unit [] (p false) (fun _ -> q)


fn test (b:bool)
  requires p b
  ensures  q
{
  match b {
    true -> {
      (* Rewrite added by checker *)
      // rewrite each b as true;
      foo1 ();
    }
    false -> {
      (* Rewrite added by checker *)
      // rewrite each b as false;
      foo2 ();
    }
  }
}




fn test_if (b:bool)
  requires p b
  ensures  q
{
  if b {
    (* Rewrite added by checker *)
    // rewrite each b as true;
    foo1 ();
  } else {
    (* Rewrite added by checker *)
    // rewrite each b as false;
    foo2 ();
  }
}

