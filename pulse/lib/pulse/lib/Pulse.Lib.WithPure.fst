module Pulse.Lib.WithPure
#lang-pulse
open Pulse.Lib.Core
open Pulse.Main


let with_pure
  (p : prop)
  (v : squash p -> slprop)
: slprop
= exists* h. v h
// Alternative definition:
// = exists* v'. tag v' ** pure (p /\ v' == v ())
// much easier to work with, but proving the size wasn't obvious.

let with_pure_timeless
  (p : prop)
  (v : squash p -> slprop)
: Lemma (requires forall s. timeless (v s))
        (ensures  timeless (with_pure p v))
        [SMTPat (timeless (with_pure p v))]
= assert_norm (with_pure p v == (exists* h. v h))

ghost fn on_with_pure_elim l (p: prop) (v: squash p -> slprop)
  requires on l (with_pure p v)
  ensures with_pure p (fun _ -> on l (v ()))
{
  ghost_impersonate l (on l (with_pure p v)) (with_pure p (fun _ -> on l (v ()))) fn _ {
    on_elim (with_pure p v);
    unfold with_pure p v;
    with h. assert v h;
    let h' = h;
    rewrite v h as v ();
    on_intro (v ());
  }
}

ghost fn on_with_pure_intro l (p: prop) (v: squash p -> slprop)
  requires with_pure p (fun _ -> on l (v ()))
  ensures on l (with_pure p v)
{
  ghost_impersonate l (with_pure p (fun _ -> on l (v ()))) (on l (with_pure p v)) fn _ {
    on_elim _;
    fold with_pure p v;
    on_intro (with_pure p v);
  }
}

let is_send_across_with_pure p v #_ = Tactics.Typeclasses.solve

ghost
fn intro_with_pure
  (p : prop)
  (v : squash p -> slprop)
  (_ : squash p)
  requires v ()
  ensures  with_pure p v
{
  assert (v ());
  fold (with_pure p v);
}



ghost
fn squash_single_coerce
  (p : prop)
  (v : squash p -> slprop)
  (s : squash p)
  requires v s
  ensures pure p
  ensures v ()
{
  rewrite v s as v ();
  ();
}



ghost
fn elim_with_pure
  (p : prop)
  (v : squash p -> slprop)
  requires with_pure p v
  returns  s : squash p
  ensures  v ()
{
  unfold (with_pure p v);
  with s. assert (v s);
  squash_single_coerce p v s;
  ()
}

