(* Section 30.  A function that *returns* a function pointer.

   [fixedb] has one field, so section 5.2 collapses it to that field's type
   and [mk_arg : U8.t -> fixedb] becomes [U8.t -> (U8.t -> SZ.t)].  Nothing is
   wrong with that -- C writes it as a function returning a pointer to a
   function -- but the trailing arrow made section 25's eta expansion read
   [mk_arg] as still owing an argument.  Expanded to arity two, its callers,
   correct at arity one, became partial applications and were rejected as
   closures.

   The two shapes below are the ones that regressed: a nullary maker and a
   maker that takes an argument it does not put in the record.  [pick] is the
   case the fix must *not* break -- a genuine chain, where the definition is
   parameterless and every caller does supply both arguments, so the expansion
   section 25 exists for still has to happen.

   [main] checks its own answers so that a wrong function pointer is a nonzero
   exit rather than something to be read out of the generated C. *)
module PulseFnPtrRet
#lang-pulse

open Pulse
module SZ = FStar.SizeT
module U8 = FStar.UInt8

let measure_one (_: U8.t) : SZ.t = 1sz
let measure_wide (x: U8.t) : SZ.t = SZ.uint32_to_sizet (FStar.Int.Cast.uint8_to_uint32 x)

noeq
type fixedb = { fmeasure: U8.t -> SZ.t }

let mk_unit () : fixedb = { fmeasure = measure_one }
let mk_arg (_: U8.t) : fixedb = { fmeasure = measure_wide }

(* A parameterless definition of arrow type, used only at full arity: this one
   must still be expanded, or it is emitted as a function-pointer variable and
   its callers come out eta-short. *)
let pick : U8.t -> SZ.t = measure_wide

fn use_unit (x: U8.t)
  returns n: SZ.t
{
  let b = mk_unit ();
  b.fmeasure x
}

fn use_arg (x: U8.t)
  returns n: SZ.t
{
  let b = mk_arg x;
  b.fmeasure x
}

fn use_pick (x: U8.t)
  returns n: SZ.t
{
  pick x
}

fn main ()
  returns r: SZ.t
{
  let a = use_unit 7uy;
  let b = use_arg 7uy;
  let c = use_pick 9uy;
  if (SZ.(a =^ 1sz) && SZ.(b =^ 7sz) && SZ.(c =^ 9sz)) { 0sz } else { 1sz }
}
