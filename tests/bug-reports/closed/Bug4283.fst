module Bug4283

#lang-pulse
open Pulse

assume val a : slprop
assume val b : slprop
assume val c : slprop

assume val lem () : b == c

[@@pulse_intro]
ghost
fn a_to_b ()
  requires a
  ensures b
{
  admit();
}

fn test ()
  requires a
  ensures c
{
  lem ();
  ();
  // a_to_b ();
  rewrite b as c;
  ()
}

(* Make sure we are checking squashes *)
assume val proven : prop -> slprop

[@@pulse_intro]
ghost
fn prove (#p:prop) (_ : squash p)
  ensures proven p
{
  admit()
}

ghost
fn test_squash1 ()
{
  assert proven True;
  drop_ (proven _);
}

ghost
fn test_squash2 ()
{
  assert proven (forall x. 1 + x > x);
  drop_ (proven _);
}

[@@expect_failure [19]]
ghost
fn test_squash3 ()
{
  assert proven False;
  drop_ (proven _);
}
