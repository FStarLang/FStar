(* Pulse.Lib.Closure under --codegen C: the result of [call] is a code
   pointer only C can call, so passing it on as a value must be refused. *)
module PulseClosureEscape
#lang-pulse

open Pulse
module U32 = FStar.UInt32
module C = Pulse.Lib.Closure

let apply (f: U32.t -> U32.t) (x: U32.t) : U32.t = f x

let double (x: U32.t) : U32.t = U32.add_mod x x

fn main ()
  returns r: U32.t
{
  let c = C.alloc #(U32.t -> U32.t) double;
  let f = C.call c;
  let r = apply f 21ul;
  C.free c;
  r
}
