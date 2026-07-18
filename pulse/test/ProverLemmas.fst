module ProverLemmas
#lang-pulse
open Pulse

let foo (p: slprop) : slprop = p

assume val pred1 : prop
assume val pred2 : p:prop { pred1 ==> p }

[@@expect_failure]
ghost fn foo_demo ()
  requires foo (pure pred1)
  ensures foo (pure pred2)
{}

[@@pulse_eager_elim]
ghost fn foo_elim (q: prop)
  requires foo (pure q)
  ensures pure q
{
  unfold foo;
}

[@@expect_failure [228]]
ghost fn foo_intro (q: prop)
  requires pure q
  ensures foo (pure q)
{
  fold foo (pure q);
}

[@@pulse_eager_intro]
ghost fn foo_intro (q: prop)
  requires pure q
  ensures foo (pure q)
{
  #set-options "--ext pulse:prover_lemmas=false" {
    fold foo (pure q);
  }
}

ghost fn foo_demo ()
  requires foo (pure pred1)
  ensures foo (pure pred2)
{}

let bar (p: slprop) = p

[@@pulse_intro]
ghost fn foo_of_bar p
  requires bar p
  ensures foo p
{
  unfold bar p;
  fold foo p;
}

[@@pulse_intro]
ghost fn bar_of_foo p
  requires foo p
  ensures bar p
{
  unfold foo p;
  fold bar p;
}

ghost fn foo_of_bar_use p q
  requires bar p
  requires foo q
  ensures foo p
  ensures bar q
{}

[@@pulse_eager_intro]
ghost fn bar_star p q
  requires bar p
  requires bar q
  ensures bar (p ** q)
{
  unfold bar p;
  unfold bar q;
  fold bar (p ** q);
}

[@@expect_failure [228]]
ghost fn uvar_loop p
  requires p
{
  unfold bar;
}