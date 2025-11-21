module Pulse.Lib.WithPure
#lang-pulse
open Pulse.Lib.Core
open Pulse.Lib.Send
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

ghost fn on_with_pure_elim l (p: prop) (v: squash p -> slprop)
  requires on l (with_pure p v)
  ensures with_pure p (fun _ -> on l (v ()))

ghost fn on_with_pure_intro l (p: prop) (v: squash p -> slprop)
  requires with_pure p (fun _ -> on l (v ()))
  ensures on l (with_pure p v)

instance val is_send_across_with_pure #b #g (p:prop) v {| (x:squash p -> is_send_across #b g (v x)) |} : is_send_across g (with_pure p v)
instance placeless_with_pure (p:prop) v {| inst: (x:squash p -> placeless (v x)) |} : placeless (with_pure p v) =
  is_send_across_with_pure p v #inst
instance is_send_with_pure (p:prop) v {| inst: (x:squash p -> is_send (v x)) |} : is_send (with_pure p v) =
  is_send_across_with_pure p v #inst

ghost
fn intro_with_pure
  (p : prop)
  (v : squash p -> slprop)
  (_ : squash p)
  requires v ()
  ensures  with_pure p v

ghost
fn elim_with_pure
  (p : prop)
  (v : squash p -> slprop)
  requires with_pure p v
  returns  _ : squash p
  ensures  v ()