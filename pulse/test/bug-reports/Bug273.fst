module Bug273

#lang-pulse
open Pulse

fn test ()
  requires emp
  returns o : option int
  ensures emp
{
  None
}
