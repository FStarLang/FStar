module ProverLemmas
#lang-pulse
open Pulse

let foo (p: slprop) : slprop = p

[@@expect_failure]
ghost fn foo_demo ()
  requires foo (pure (1 < 0))
  ensures foo (pure (forall (x y: nat). x == y))
{}

[@@pulse_eager_intro]
ghost fn foo_intro (q: prop)
  requires pure q
  ensures foo (pure q)
{
  fold foo (pure q);
}

[@@pulse_eager_elim]
ghost fn foo_elim (q: prop)
  requires foo (pure q)
  ensures pure q
{
  unfold foo;
}

ghost fn foo_demo ()
  requires foo (pure (1 < 0))
  ensures foo (pure (forall (x y: nat). x == y))
{}