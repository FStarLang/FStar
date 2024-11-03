module Pulse.Lib.WithPure
#lang-pulse
open Pulse.Lib.Core
open Pulse.Main

val with_pure
  (p : prop)
  (v : squash p -> slprop)
: slprop

val with_pure_timeless
  (p : prop)
  (v : squash p -> slprop)
: Lemma (requires forall s. timeless (v s))
        (ensures  timeless (with_pure p v))
        [SMTPat (timeless (with_pure p v))]
ghost
fn intro_with_pure
  (p : prop)
  (v : squash p -> slprop)
  (_ : squash p)
  requires pure p ** v ()
  ensures  with_pure p v

ghost
fn elim_with_pure
  (p : prop)
  (v : squash p -> slprop)
  requires with_pure p v
  returns  _ : squash p
  ensures  v ()