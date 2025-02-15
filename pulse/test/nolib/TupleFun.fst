module TupleFun

#lang-pulse
open Pulse.Nolib

assume val foo : int -> slprop
assume val bar : int -> slprop

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


fn call ()
  requires emp
  ensures emp
{
  let Mktuple2 x y = ret2 ();
  usefoo x;
  usebar y;
}

[@@expect_failure]
fn call_no_mut ()
  requires emp
  ensures emp
{
  let mut Mktuple2 x y = ret2 ();
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
