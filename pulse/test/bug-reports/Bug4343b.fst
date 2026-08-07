module Bug4343b
open Pulse
#lang-pulse

fn decr (r: ref int) (#w: erased int)
  requires pts_to r w ** pure (reveal w > 0)
  returns b: bool
  ensures exists* (v: int). pts_to r v ** pure (v == reveal w - 1) ** pure (b == (v > 0))
{
  let x = !r;
  r := x - 1;
  let y = !r;
  (y > 0)
}

divergent
fn count_down ()
  requires emp
  returns res: int
  ensures pure (res == 0)
{
  let mut r = 5;
  while (decr r)
    invariant (exists* (v: int). pts_to r v ** pure (1 <= v /\ v <= 5))
  { () };
  let v = !r;
  v
}
