module MetaArg

#lang-pulse
open Pulse
open FStar.Tactics.V2

fn foo
  (#[exact (`0)] x : int)
  (_:unit)
  returns r : (r : int { r == x })
{
  x
}

fn test ()
{
  let x = foo ();
  assert (pure (x == 0));
  ()
}

fn test2 ()
{
  let x = foo #2 ();
  assert (pure (x == 2));
  ()
}
