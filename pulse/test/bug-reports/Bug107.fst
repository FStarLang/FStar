module Bug107
#lang-pulse

open Pulse.Lib.Pervasives

val foo : int -> int -> slprop
let foo x y = emp


fn test0 ()
  requires foo 1 2
  ensures emp
{
  unfold foo 1 2;
  ()
}



fn test1 ()
  requires foo 1 2
  ensures emp
{
  unfold foo;
  ()
}



fn test2 ()
  requires foo 1 2
  ensures emp
{
  unfold foo 1;
  ()
}


fn test3 ()
  requires foo 1 2
  ensures emp
{
  unfold foo 1 _;
  ()
}


fn test4 ()
  requires foo 1 2
  ensures emp
{
  unfold foo _ 2;
  ()
}

