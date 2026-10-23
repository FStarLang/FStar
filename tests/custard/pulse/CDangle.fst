module CDangle
#lang-pulse
open Pulse
module U32 = FStar.UInt32

type col = | R | G | B

(* Section 6.  An [if] with no [else] as the [then] arm of an [if] that has
   one.  The inner statement fits on a line and so would be written unbraced,
   and C's [else] binds to the nearest unmatched [if]: the [else] meant for
   [a] would attach to [b] instead, and [f false true] would fall through
   silently instead of returning 2. *)

fn f (a b : bool)
  returns res : U32.t
{
  let mut r = 0ul;
  if a ensures exists* v. r |-> v { if b { r := 1ul } } else { r := 2ul };
  !r
}

(* The same shape reached through a match, where the arm that follows is
   written [else if] rather than [else]. *)
fn g (x : col) (b : bool)
  returns res : U32.t
{
  let mut r = 0ul;
  match x ensures exists* v. r |-> v {
    R -> { if b { r := 1ul } }
    G -> { r := 2ul }
    B -> { r := 3ul }
  };
  !r
}

(* A non-zero exit is the failure: the [.dcran] rule runs the program and
   asks for status 0. *)
fn main ()
  returns res : U32.t
{
  let a1 = f true true;
  let a2 = f true false;
  let a3 = f false true;
  let b1 = g R true;
  let b2 = g R false;
  let b2' = g G false;
  let b3 = g B false;
  if (a1 = 1ul && a2 = 0ul && a3 = 2ul &&
      b1 = 1ul && b2 = 0ul && b2' = 2ul && b3 = 3ul)
  { 0ul } else { 1ul }
}
