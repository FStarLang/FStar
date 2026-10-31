module UnitFnValue
#lang-pulse
open Pulse.Lib.Pervasives
module U32 = FStar.UInt32

(* A top-level function with a [unit] parameter in the middle, passed as a
   function value: its definition and the arrow type it is passed at must
   agree on whether that parameter is there. *)
let cb = U32.t -> unit -> U32.t -> stt U32.t emp (fun _ -> emp)

fn g (x:U32.t) (u:unit) (y:U32.t)
returns U32.t
{
  U32.add_mod x y
}

fn h (f: cb) (x:U32.t)
returns U32.t
{
  f x () 1ul
}

fn test (x:U32.t)
returns U32.t
{
  h g x
}

fn main ()
  returns r: FStar.Int32.t
{
  0l
}
