(* Section 91.  A control for a reported gap rather than a fix for one.

   Kuiper reports that [[@@@monomorphize]] on a [szp] binder of a Pulse [fn]
   is accepted and then silently ignored -- the classification stanza is
   byte-identical with and without it, all [Poly], and a user who hits error
   390 therefore has no way to ask for the demand explicitly.

   That is not true of a Pulse [fn] as such, which is what this pins: the
   attribute is written on the *lambda*, Pulse's [tm_arrow] does not carry it
   into the elaborated type, and section 33.3 unions the two positionally for
   exactly this reason.  Two specializations come out.

   So whatever suppresses it in their build is a property of how the
   definition they annotated is declared, not of Pulse binders, and this test
   is what makes that a measurement rather than a claim. *)
module MonoAttr
#lang-pulse
open Pulse
module SZ = FStar.SizeT

fn f ([@@@FStar.Attributes.monomorphize] n: SZ.t) (r: ref SZ.t)
  requires exists* v. r |-> v
  ensures  exists* v. r |-> v
{
  r := n;
}

fn main ()
  returns x: FStar.Int32.t
{
  let mut r = 3sz;
  f 16sz r;
  f 32sz r;
  let v = !r;
  if (SZ.eq v 32sz) { 0l } else { 1l }
}
