module Test.JoinInference
#lang-pulse
open Pulse
open FStar.Mul


fn do_something (x:ref int) (#v:int)
requires x |-> v
ensures x |-> (v + 5)
{
    x := !x + 1;
    x := !x + 1;
    x := !x + 1;
    x := !x + 1;
    x := !x + 1;
}

fn test_join (x:ref int) (b:bool)
requires x |-> 'v
ensures x |-> (if b then 'v + 2 else 'v + 3)
{
  if (b)
  {
    x := !x + 1;
  }
  else
  { 
    x := !x + 1;
    x := !x + 1;
  };
  x := !x + 1;
}

fn test_join2 (x:ref int) (b:bool)
requires x |-> 'v
ensures x |-> (if b then 'v + 2 else 'v + 3)
{
  let mut res = 0;
  if (b)
  {
    x := !x + 1;
    res := !x;
  }
  else
  { 
    x := !x + 1;
    x := !x + 1;
    res := !x;
  };
  x := !res + 1;
}

fn test_join3 (x:ref int) (b:bool) (i:iname) (p:slprop)
requires (x |-> 'v)
ensures x |-> (if b then 'v + 2 else 'v + 3)
{
  let res = 
      if (b)
      {
        x := !x + 1;
        !x;
      }
      else
      { 
        x := !x + 1;
        x := !x + 1;
        !x;
      };
  x := res + 1;
}