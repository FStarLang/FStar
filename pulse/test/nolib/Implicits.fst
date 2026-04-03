module Implicits

#lang-pulse
open Pulse.Nolib

class deq (a:Type) = {
  (=?) : a -> a -> bool;
}

instance deq_int : deq int = {
  (=?) = (fun x y -> x = y);
}

fn foo1 (a:Type0) {| deq a |}
{ () }

fn foo2 (#a:Type0) {| deq a |}
{ () }

fn foo3 (#a:Type0) {| deq a |} (x:a)
{ () }

fn foo4 (#a:Type0) (x:a) {| deq a |}
{ () }

fn foo5 (x:int) (#_:unit)
{ () }

(* Would be nice if everything here worked. *)
fn test () {
  // foo5 1; (* can't resolve the unit *)
  // foo1 int; (* pulse claims partially applied *)
  foo1 int #deq_int;
  foo1 int #_;
  // foo2 #int; (* pulse claims partially applied *)
  foo2 #int #_;
  foo3 123;
  // foo4 123; (* pulse claims partially applied *)
  foo4 123 #_;
  ();
}
