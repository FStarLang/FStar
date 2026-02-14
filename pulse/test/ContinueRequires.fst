module LoopRequires
open Pulse
#lang-pulse

fn dice_roll () returns heads: bool { true } 

ghost fn assert_ p // without adding `_: squash p` to environment
  requires pure p
{}

fn continue_requires () {
  let mut x = false;
  while ({ assert_ (!x == false); true })
    invariant live x
    requires (!x == false)
    ensures (!x == true)
  {
    assert pure (!x == false);
    if (dice_roll ()) {
      x := true;
      assert pure (!x == true);
      break;
    }
  };
  assert pure (!x == true);
}