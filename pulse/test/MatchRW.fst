module MatchRW
#lang-pulse

open Pulse.Lib.Pervasives

assume
val p ([@@@mkey] b : bool) : slprop

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

assume
val r ([@@@mkey] x : int) : slprop

assume
val foo3 (x:int) : stt_ghost unit [] (r x) (fun _ -> q)

assume
val f (x:int) : Tot int

#push-options "--no_smt"

fn test_rewrites_to (x:int)
  requires r x
  ensures q
{
  match x {
    y -> {
      foo3 y;
    }
  }
}

fn test_compound_rewrite (x:int)
  requires r (f x)
  ensures q
{
  match (f x) {
    y -> {
      foo3 y;
    }
  }
}

#pop-options
