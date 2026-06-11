module Bug4314

#lang-pulse
open Pulse

assume val q : prop

assume val lem () : Lemma (ensures q)
fn test ()
  ensures pure q
  { lem (); }

assume val slem () : squash q
fn test2 ()
  ensures pure q
  { slem (); }

assume val slem0 : squash q
fn test3 ()
  ensures pure q
  { slem0; }

assume val plem () : ghost fn ensures pure q
fn ptest ()
  ensures pure q
  { plem (); }
