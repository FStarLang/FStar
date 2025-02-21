module NoRewrite

#lang-pulse
open Pulse.Nolib

assume val foo : [@@@equate_strict]_:int -> slprop

fn test1 (x : int)
  requires foo x
  ensures  foo x
{
  match x {
    norewrite y -> {
      assert foo x;
      ();
    }
  }
}

fn test2 (x : int)
  requires foo x
  ensures  foo x
{
  match x {
    y -> {
      assert foo y;
      rewrite each y as x; (* restore *)
    }
  }
}

assume val bar : [@@@equate_strict]_:option int -> slprop

fn test3 (x : option int{Some? x})
  requires bar x
  ensures  bar x
{
  let Some xx = x;
  assert (bar (Some xx));
  rewrite each Some xx as x; (* restore *)
}

fn test4 (x : option int{Some? x})
  requires bar x
  ensures  bar x
{
  norewrite let Some xx = x;
  assert (bar x);
}
