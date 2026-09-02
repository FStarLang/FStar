(* Section 34.3.  A Pulse [fn] block passed as an argument, capturing state
   that is not one of its parameters.

   Round 40's reporter checked that [@@@monomorphize] on a [fn] binder now
   works on a real separation-logic loop combinator, and observed that the
   captures -- a [ref] and a plain value, neither of them a loop parameter --
   come out as parameters of the specialized loop.  This is that observation
   reduced to Pulse's own library, so that it is tested here rather than only
   downstream.

   What has to hold for the C to be right: the loop is compiled once per
   *body*, not once per call, and the body's free variables have to travel to
   it.  [r] and [k] are free in the block and bound in [accum], so they can
   only arrive as arguments to the specialized [for_upto]; if either were
   dropped or captured from the wrong frame the answer would change, and
   [main] checks the answer.

   The invariant is an explicit [slprop] parameter rather than a formula
   mentioning a [ref] parameter, and that is forced rather than stylistic.
   Written the other way --

     fn for_upto (r : ref U32.t) (n : U32.t)
                 ([@@@monomorphize] body : x:U32.t -> stt unit (exists* v. r |-> v) ...)

   -- the body's type mentions [r], so section 3.1 rule 5 carries the demand
   from [body] to [r], and [r] is a runtime parameter of [accum]: error 364,
   "there is nothing to specialize on".  Naming the invariant instead puts a
   *ghost* binder in the demand's way, which rule 1 drops before rule 5 can
   reach through it.  Kuiper's [for_loop'] is written with the invariant
   passed explicitly for the same reason. *)
module PulseForCapture
#lang-pulse

open Pulse
module U32 = FStar.UInt32

(* The body's specification mentions [r], so the combinator is state-passing
   in exactly the way Kuiper's is: the block is not closed, and its frame is
   named by a parameter of the combinator rather than by the block. *)
divergent
fn for_upto (n : U32.t) (inv : slprop)
            ([@@@FStar.Attributes.monomorphize]
             body : (x:U32.t -> stt unit inv (fun _ -> inv)))
  requires inv
  ensures  inv
{
  let mut i = 0ul;
  while (let vi = !i; U32.lt vi n)
  invariant exists* vi. i |-> vi ** inv
  {
    let vi = !i;
    body vi;
    i := U32.add_mod vi 1ul;
  }
}

(* [k] is captured and [r] is captured; the index [x] is ignored, so nothing
   the loop supplies can stand in for either. *)
divergent
fn accum (r : ref U32.t) (k : U32.t)
  requires exists* v. r |-> v
  ensures  exists* v. r |-> v
{
  for_upto 10ul (exists* v. r |-> v)
    fn (x:U32.t) { let v = !r; r := U32.add_mod v k };
}

divergent
fn main ()
  returns r: U32.t
{
  let mut c = 0ul;
  accum c 3ul;
  let v = !c;
  (* ten iterations of [+ 3] *)
  if (v = 30ul) { 0ul } else { 1ul }
}
