module Ambig
#lang-pulse

open Pulse.Nolib

assume val p : int -> slprop

(* An example of ambiguity in Pulse. Note: if the foo
function instead took an existential as a precondition,
then there's no easy way to disambiguate... *)

assume
val foo () (#x:erased int)
  : stt unit (p x) (fun _ -> emp)

[@@expect_failure]

fn ambig ()
  requires p 1 ** p 2
  ensures  p 1
{
  foo ();
  ()
}


(* TODO: can we support a syntax like:

     from p 1.
       foo ();
       
     or

     framing p 2.
       foo ();
    
    which would force the pre of foo() to be proven from p 1? Essentially
    a small block. *)


fn ok1 ()
  requires p 1 ** p 2
  ensures p 2
{
  foo () #1;
  ()
}



fn ok2 ()
  requires p 1 ** p 2
  ensures p 1
{
  foo () #2;
  ()
}


(* This is "ambiguous" in that there are two (p 1), but since they are
syntactically equal we do not complain. *)

fn ok3 ()
  requires p 1 ** p 1
  ensures emp
{
  foo ();
  foo ();
  ()
}


[@@allow_ambiguous]
assume val foo2 () (#x #y:erased int)
  : stt unit (p x ** p y) (fun _ -> emp)

(* This one is more ambiguous... but would probably be OK. Could we not fail here?
This is a problem for any use of gather, really. *)

fn ok4 ()
  requires p 2 ** p 1
  ensures emp
{
  foo2 ();
  ()
}


(* This one is awkward due to the existentials. It can work
by asserting a _syntactically equal_ slprop to obtain one of the two
variables and then disambiguate. *)

fn ok5 ()
  requires (exists* x. p (12+x)) **
           (exists* y. p (34+y))
  ensures emp
{
  with x.
    assert p (12+x);
  foo () #(12+x);
  foo ();
}


(* If we do not have a way to distinguish the two existentials,
as below, we can use an ambiguous auxiliary function. *)

[@@allow_ambiguous]
assume
val foo' () (#x:erased int)
  : stt unit (p x) (fun _ -> emp)


fn ok6 ()
  requires (exists* x. p x) **
           (exists* y. p y)
  ensures emp
{
  foo' ();
  foo ();
}

