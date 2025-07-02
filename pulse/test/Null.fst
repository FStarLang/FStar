module Null

#lang-pulse
open Pulse
open Pulse.Lib.Box
module Box = Pulse.Lib.Box
module Ref = Pulse.Lib.Reference

(*
PRESERVES(null_or_live(x));
int foo(int *x) {
  if (x == NULL) {
    return 0;
  } else {
    return *x;
  }
}
*)

let x : ref int = Pulse.Lib.Reference.null
let y () : box int = Box.null

fn foo ()
  returns r : box int
{
  Box.null
}

// This should maybe go into the Pulse library or a prelude.
unfold
let live #a (r : ref a) =
  exists* v. r |-> v

// Idem
unfold
let null_or_live #a (r : ref a) =
  if Ref.is_null r
  then emp
  else live r

fn test (x : ref int)
  preserves null_or_live x
  returns int
{
  if (Ref.is_null x) {
    rewrite emp as null_or_live x;
    0
  } else {
    let res = Ref.(!x);
    rewrite live x as null_or_live x;
    res
  }
}
