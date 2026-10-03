(* Section 33.2 and 33.3.  A [@@@monomorphize] annotation on the binder of a
   Pulse [fn], and what has to be true for it to do anything.

   Two independent things were in the way, and both are needed for even this
   much.

   The attribute is written on the *lambda*, and Pulse's [tm_arrow] builds the
   elaborated arrow type without carrying binder attributes across, so the
   annotation was on the definition and absent from its type.  A
   classification that reads the type alone therefore ignored it silently:
   deleting the attribute produced a byte-identical dump.  Section 33.3 unions
   the two sources.

   And a Pulse [fn] of two binders extracts eta-contracted -- [eta_reduce]
   moves the trailing [r] into the result arrow -- so the call to it is a
   partial application, which C rejects before specialization can help.
   Section 33.1 and 33.2 put the binder back.

   [main] checks its own answer, so a specialization that closed over the
   wrong value is a nonzero exit rather than something to read out of the
   generated C. *)
module PulseMono
#lang-pulse

open Pulse
module U32 = FStar.UInt32

fn apply_twice ([@@@FStar.Attributes.monomorphize] f : (x:U32.t -> U32.t))
               (r : ref U32.t)
  requires exists* v. r |-> v
  ensures  exists* v. r |-> v
{
  let v = !r;
  r := f (f v);
}

fn add_k (k : U32.t) (r : ref U32.t)
  requires exists* v. r |-> v
  ensures  exists* v. r |-> v
{
  apply_twice (fun x -> U32.add_mod x k) r;
}

fn run ()
  returns v: U32.t
{
  let mut r = 5ul;
  add_k 3ul r;
  !r
}

fn main ()
  returns r: U32.t
{
  let v = run ();
  if (v = 11ul) { 0ul } else { 1ul }
}
