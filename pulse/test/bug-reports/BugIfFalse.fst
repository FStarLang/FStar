module BugIfFalse
#lang-pulse
open Pulse.Lib.Pervasives

fn text ()
requires emp
ensures emp
{
  if (false)
  {
    ()
  }
  else
  {
    ()
  }
}