module PulseGlobalArrayLocal
#lang-pulse
open Pulse
module A  = Pulse.Lib.Array
module G  = Pulse.Lib.GlobalArray
module US = FStar.SizeT
module U8 = FStar.UInt8

(* Section 71.4.  A braced initializer is not an expression in C: it may
   appear only where an object is being declared.  The OCaml and karamel
   backends accept this same program -- OCaml has an array literal and
   karamel has EBufCreateL -- which is why the refusal lives in PrintC rather
   than in the rule. *)

fn main () returns r:US.t
{
  let t = G.mk_static_array [1uy; 2uy];
  let a = G.array_of_static_array t;
  with p s. assert (A.pts_to a #p s);
  A.pts_to_len a;
  let x = A.op_Dot_Lparen_Rparen a 0sz;
  drop_ (A.pts_to a #p s);
  if (U8.(x =^ 1uy)) { 0sz } else { 1sz }
}
