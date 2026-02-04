module TupleFun

#lang-pulse
open Pulse.Nolib

assume val foo : int -> slprop
assume val bar : int -> slprop

fn usefoo (x:int)
  requires foo x
{
  admit()
}

fn usebar (x:int)
  requires bar x
{
  admit()
}

fn ret2 ()
  returns xy : int & int
  ensures foo (fst xy)
  ensures bar (snd xy)
{
  admit();
}

(* This works without SMT given that the pulse prover will
simplify tuple projections, and also that we rewrite the result
of the call into (x,y) after the match (desugared from the let). *)
#push-options "--no_smt"
fn call ()
{
  let x, y = ret2 ();
  usefoo x;
  usebar y;
}
#pop-options

[@@expect_failure]
fn call_no_mut ()
{
  let mut x, y = ret2 ();
  usefoo x;
  usebar y;
}

fn retsome ()
  returns  o : option int
  ensures  pure (Some? o)
{
  Some 12;
}

fn call_opt ()
{
  let Some x = retsome ();
  ()
}
