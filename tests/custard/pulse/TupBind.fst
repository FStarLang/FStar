module TupBind
#lang-pulse
open Pulse.Lib.Pervasives
module SZ = FStar.SizeT

fn prim (x: SZ.t) requires emp returns res: (SZ.t & SZ.t) ensures emp
{ (x, x) }

inline_for_extraction
fn layer1 (x: SZ.t) requires emp returns res: (SZ.t & SZ.t) ensures emp
{ let a, b = prim x; (a, b) }

inline_for_extraction
fn layer2 (x: SZ.t) requires emp returns res: (SZ.t & SZ.t) ensures emp
{ let a, b = layer1 x; (a, b) }

(* Not [inline_for_extraction]: here the tuple really is the return value, so
   there is nothing to collapse into a caller.  The reporter expected this one
   to need a second peephole, [C x.f1 ... x.fn -> x], and it does not: the IR
   says [match prim x with C(a,b) -> C(a,b)], the eta law rewrites that to
   [prim x] outright, and the wrapper disappears into a tail call. *)
fn standalone (x: SZ.t) requires emp returns res: (SZ.t & SZ.t) ensures emp
{ let a, b = prim x; (a, b) }

fn top (x: SZ.t) requires emp returns r: SZ.t ensures emp
{ let a, b = layer2 x; a }

fn main ()
  returns x: FStar.Int32.t
{
  let a = top 7sz;
  let c, d = standalone 9sz;
  if (SZ.eq a 7sz && SZ.eq c 9sz && SZ.eq d 9sz) { 0l } else { 1l }
}
