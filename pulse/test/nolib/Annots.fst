module Annots

#lang-pulse
open Pulse.Nolib

assume val res : int -> slprop

(* Relaxed syntax for computation types, allowing to omit requires/ensures/returns,
   and imposing a less strict order between them. *)

fn foo1 ()
{
  ();
}

fn foo2 ()
  returns int
{
  1
}

fn foo2' ()
  returns _ : int
{
  1
}

[@@expect_failure]
fn no_multiple_ret ()
  preserves res 1
  preserves res 2
  returns int
  returns int
{
  1
}

[@@expect_failure]
fn wrong_order1 ()
  returns int
  preserves res 1
{
  1
}

[@@expect_failure]
fn wrong_order2 ()
  preserves res 1
{
  1
}

[@@expect_failure]
fn wrong_order3 ()
  returns bool
  requires res 1
{
  1
}

(* Reject! It would refer to the argument x
and not the return value! *)
[@@expect_failure]
ghost
fn wrong_order4 (x:iname)
  returns x : iname
  opens [x]
{
  admit()
}

[@@expect_failure]
fn wrong_order2 ()
  preserves res 1
{
  1
}

[@@expect_failure]
fn wrong_order3 ()
  returns bool
  requires res 1
{
  1
}


fn foo4 ()
  preserves res 1
  preserves res 2
  returns int
{
  1
}

fn foo5 ()
  requires res 1
  returns v : int
  ensures res v
{
  1
}

[@@expect_failure [72]] // desugaring failure, precondition
fn foo6 ()
  preserves res v
  returns v : int
{
  1
}

(* tuples *)

fn tup1 ()
  returns int & int
{
  (1,2)
}

fn tup2 ()
  returns t : int & int
{
  (1,2)
}
