module CalcInPulse
#lang-pulse

(* Regression test: F* calculational proofs (`calc`) can be written in their
   bare form, as statements, directly inside a Pulse `fn` body. Previously the
   Pulse grammar only accepted a `calc` term when it was wrapped, e.g.
   `(calc (==) { ... })` or `let _ = calc (==) { ... }`; the bare form that
   works in ordinary F* raised a syntax error. *)

open Pulse.Lib.Pervasives

(* The bare form: this is what used to fail to parse. *)
fn test_bare (x:int)
  requires emp
  ensures emp
{
  calc (==) {
    x + 0;
    == {}
    x;
  };
  ()
}

(* A calc with several steps, used to discharge a fact that the surrounding
   proof then relies on for its postcondition. *)
fn test_used (x:int)
  requires emp
  returns y:int
  ensures pure (y == x)
{
  calc (==) {
    (x + 1) - 1;
    == {}
    x + (1 - 1);
    == {}
    x;
  };
  (x + 1) - 1
}

(* The previously-supported wrapped forms must keep working. *)
fn test_paren (x:int)
  requires emp
  ensures emp
{
  (calc (==) {
    x + 0;
    == {}
    x;
  });
  ()
}

fn test_let (x:int)
  requires emp
  ensures emp
{
  let _ = calc (==) {
    x + 0;
    == {}
    x;
  };
  ()
}
