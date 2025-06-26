module Null

#lang-pulse
open Pulse

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

// This should maybe go into the Pulse library or a prelude.
unfold
let live #a (r : ref a) =
  exists* v. r |-> v

// Idem
unfold
let null_or_live #a (r : ref a) =
  if is_null r
  then emp
  else live r

fn foo (x : ref int)
  preserves null_or_live x
  returns int
{
  if (is_null x) {
    0
  } else {
    unfold null_or_live x;
    rewrite each is_null #int x as false;
    let res = !x;
    rewrite live x as null_or_live x;
    res
  }
}
