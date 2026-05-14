module Bug4256
#lang-pulse
open Pulse

let foo ([@@@mkey] m: nat) (n: nat) : slprop =
  pure (m = n)

[@@pulse_intro]
ghost fn foo_refl (m: nat)
  ensures foo m m
{
  fold foo m m
}

[@@expect_failure [19]]
ghost fn uhoh_intro ()
  ensures pure False
{
  assert foo 2 3;
  unfold foo
}

let bar ([@@@mkey] m: nat) (n: nat) : slprop =
  pure (m = n)

[@@pulse_eager_intro]
ghost fn bar_refl (m: nat)
  ensures bar m m
{
  fold bar m m
}

[@@expect_failure [19]]
ghost fn uhoh_eager_intro ()
  ensures pure False
{
  assert bar 2 3;
  unfold bar
}

let baz ([@@@mkey] m: nat) (n: nat) : slprop =
  pure (m <> n)

[@@pulse_eager_elim]
ghost fn baz_refl (m: nat)
  requires baz m m
  ensures is_unreachable
{
  unfold baz m m;
  unreachable ()
}

[@@expect_failure [19]]
ghost fn uhoh_eager_elim ()
  ensures pure False
{
  fold baz 2 3;
}
