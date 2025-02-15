module TupleFun

#lang-pulse
open Pulse.Nolib

assume val foo : [@@@equate_strict]_:int -> slprop
assume val bar : [@@@equate_strict] int -> slprop

fn usefoo (x:int)
  requires foo x
  ensures emp
{
  admit()
}

fn usebar (x:int)
  requires bar x
  ensures emp
{
  admit()
}

fn ret2 ()
  requires emp
  returns xy : int & int
  ensures foo (fst xy) ** bar (snd xy)
{
  admit();
}

(* This works without SMT given that the pulse prover will
simplify tuple projections, and also that we rewrite the result
of the call into (x,y) after the match (desugared from the let). *)
#push-options "--no_smt"
fn call ()
  requires emp
  ensures emp
{
  let x, y = ret2 ();
  usefoo x;
  usebar y;
}
#pop-options

[@@expect_failure]
fn call_no_mut ()
  requires emp
  ensures emp
{
  let mut x, y = ret2 ();
  usefoo x;
  usebar y;
}

fn retsome ()
  requires emp
  returns  o : option int
  ensures  pure (Some? o)
{
  Some 12;
}

fn call_opt ()
  requires emp
  ensures emp
{
  let Some x = retsome ();
  ()
}
