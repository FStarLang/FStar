module MetaArg

#lang-pulse
open Pulse
open FStar.Tactics.V2

fn foo
  (#[exact (`0)] x : int)
  (_:unit)
  requires emp
  returns r : (r : int { r == x })
  ensures emp
{
  x
}

fn test ()
  requires emp
  ensures emp
{
  let x = foo ();
  assert (pure (x == 0));
  ()
}

fn test2 ()
  requires emp
  ensures emp
{
  let x = foo #2 ();
  assert (pure (x == 2));
  ()
}
