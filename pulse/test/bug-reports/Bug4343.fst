module Bug4343
open Pulse
#lang-pulse

(* The result of a call whose postcondition does not constrain it must not be
   existentially quantified at the slprop level: the prover has no way of
   guessing a witness for such an `exists*`. Instead the quantifier is pushed
   into the `pure` proposition. *)

fn flip_coin ()
  returns b: bool
{
  true
}

divergent
fn while_flip ()
{
  while (not (flip_coin ())) {}
}

fn if_flip ()
{
  if (true)
  {
    let b = not (flip_coin ());
    ()
  };
  ()
}

(* The pure facts constraining the escaping variable may be spread across
   nested `exists*`. *)

assume
val decr (r: ref int) (#w: erased int) : stt bool
  (pts_to r w ** pure (reveal w > 0))
  (fun b -> exists* (v:int). pts_to r v ** pure (b == (v > 0)) ** pure (v < w))

divergent
fn count_down ()
  requires emp
  returns res: int
  ensures pure (res <= 0)
{
  let mut r = 5;
  while (decr r)
    invariant (exists* (v: int). pts_to r v ** pure (1 <= v))
  { () };
  let v = !r;
  v
}
