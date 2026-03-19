module BugIfFalse
#lang-pulse
open Pulse.Lib.Pervasives

fn text ()
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