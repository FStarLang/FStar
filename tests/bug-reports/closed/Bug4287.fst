module Bug4287

#lang-pulse
open Pulse

fn foo ()
{
  let mut rr : erased real = 0.0R;
  assert pure (!rr == 0.0R);
}

fn bar()
{
  let mut rr : erased int = 0;
  let v : erased int = Pulse.Lib.Reference.read rr #_ #_;
  ()
}
