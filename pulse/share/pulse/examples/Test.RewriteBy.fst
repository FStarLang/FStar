module Test.RewriteBy
#lang-pulse

open Pulse.Lib.Pervasives
open FStar.Tactics.V2

assume val p : slprop
assume val q : slprop

let tac () : Tac unit =
   dump "test";
   tadmit ()


fn test1 ()
  requires p
  ensures  q
{
  rewrite p
       as q
       by tadmit ();
}


(* lambdas are broken, looks like F* bug? *)
[@@expect_failure]

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


let dump_trefl (s:string) : Tac unit =
  dump s;
  slprop_equiv_norm ()


fn test ()
  requires p
  ensures  p
{
  rewrite p
       as p
       by dump_trefl "test";
}

