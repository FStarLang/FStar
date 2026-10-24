(* Regression test for FStarLang/FStar#4790.

   The loop condition reads one field of a record held in [x], which splits
   the record witness across two cells. A body that writes one cell and
   [break]s must then re-establish the condition's post-state; Pulse used to
   close that state with a single [exists* v] over the record, which the
   prover instantiates from the untouched cell and then cannot match against
   the written one. *)
module BreakRecord
open Pulse
#lang-pulse
module U64 = FStar.UInt64

noeq type pair = { a: U64.t; b: U64.t }

assume val fa (x: ref pair) : ref U64.t
assume val fb (x: ref pair) : ref U64.t
assume val raw (x: ref pair) : slprop

assume val split (x: ref pair) (#v: pair)
  : stt_ghost unit emp_inames
      (pts_to x v)
      (fun _ -> raw x ** pts_to (fa x) v.a ** pts_to (fb x) v.b)

assume val join (x: ref pair) (#va #vb: U64.t)
  : stt_ghost unit emp_inames
      (raw x ** pts_to (fa x) va ** pts_to (fb x) vb)
      (fun _ -> pts_to x { a = va; b = vb })

(* Control: break without the write. *)
divergent fn break_only (x: ref pair)
  requires exists* v. pts_to x v
  ensures  exists* v. pts_to x v
{
  while (split x; (!(fa x) = 0uL))
    invariant exists* v. pts_to x v
    ensures true
  {
    break;
  };
  join x;
}

(* Control: the write without the break. *)
divergent fn write_only (x: ref pair)
  requires exists* v. pts_to x v
  ensures  exists* v. pts_to x v
{
  while (split x; (!(fa x) = 0uL))
    invariant exists* v. pts_to x v
  {
    (fa x) := 1uL;
    join x;
  };
  join x;
}

(* Control: the condition leaves the record in one cell. *)
divergent fn whole_record (x: ref pair)
  requires exists* v. pts_to x v
  ensures  exists* v. pts_to x v
{
  while ((!x).a = 0uL)
    invariant exists* v. pts_to x v
    ensures true
  {
    x := { a = 1uL; b = 0uL };
    break;
  }
}

(* Write the field the condition read, then break. *)
divergent fn write_then_break (x: ref pair)
  requires exists* v. pts_to x v
  ensures  exists* v. pts_to x v
{
  while (split x; (!(fa x) = 0uL))
    invariant exists* v. pts_to x v
    ensures true
  {
    (fa x) := 1uL;
    break;
  };
  join x;
}

(* Write the other field. *)
divergent fn write_other_field (x: ref pair)
  requires exists* v. pts_to x v
  ensures  exists* v. pts_to x v
{
  while (split x; (!(fa x) = 0uL))
    invariant exists* v. pts_to x v
    ensures true
  {
    (fb x) := 1uL;
    break;
  };
  join x;
}

(* No loop [ensures]: the break precondition then comes from the inferred
   condition postcondition instead. *)
divergent fn no_ensures (x: ref pair)
  requires exists* v. pts_to x v
  ensures  exists* v. pts_to x v
{
  while (split x; (!(fa x) = 0uL))
    invariant exists* v. pts_to x v
  {
    (fa x) := 1uL;
    break;
  };
  join x;
}

noeq type predicate_record (a:Type0) = { holds: a -> slprop }

(* The argument of a function-valued field is not the record receiver.
   Inference must preserve [p.holds v], not quantify the whole slprop. *)
divergent fn function_field_argument (p:predicate_record U64.t)
  requires exists* v. p.holds v
  ensures exists* v. p.holds v
{
  while (true)
    invariant exists* v. p.holds v
    ensures true
  {
    break;
  }
}
