module DropEmp
#lang-pulse

open Pulse.Lib.Pervasives


fn test0 (p:slprop)
  requires (if true then emp else p)
  ensures emp
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
  ensures emp
{
  ();
}

