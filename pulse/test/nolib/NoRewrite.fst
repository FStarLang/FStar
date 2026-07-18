module NoRewrite

#lang-pulse
open Pulse.Nolib

assume val foo : [@@@mkey]_:int -> slprop

fn test1 (x : int)
  preserves foo x
{
  match x {
    norewrite y -> {
      assert foo x;
      ();
    }
  }
}

fn test2 (x : int)
  preserves foo x
{
  match x {
    y -> {
      assert foo y;
      rewrite each y as x; (* restore *)
    }
  }
}

assume val bar : [@@@mkey]_:option int -> slprop

fn test3 (x : option int{Some? x})
  preserves bar x
{
  let Some xx = x;
  assert (bar (Some xx));
  rewrite each Some xx as x; (* restore *)
}

fn test4 (x : option int{Some? x})
  preserves bar x
{
  norewrite let Some xx = x;
  assert (bar x);
}
