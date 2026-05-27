module DropEmp
#lang-pulse

open Pulse.Nolib


fn test0 (p:slprop)
  requires (if true then emp else p)
{
  ();
}



fn test1 (p:slprop)
  requires (if false then emp else p)
  ensures p
{
  ();
}


[@@expect_failure]

fn test2 (p:slprop)
  requires (if true then emp else p)
  ensures p
{
  ();
}


[@@expect_failure]

fn test3 (p:slprop)
  requires (if false then emp else p)
{
  ();
}

