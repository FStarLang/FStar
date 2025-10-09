module LetMutImps

#lang-pulse
open Pulse

assume val zero : #a:Type -> a

fn test ()
{
  let mut r : int = zero;
  ();
}

fn test2 ()
{
  let mut p : ref u#0 int = null;
  ();
}

fn test3 ()
{
  let r : int = zero;
  ();
}

fn test4 ()
{
  let p : ref int = null;
  ();
}
