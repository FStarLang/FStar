(* Section 95.  [ArrInit]'s program at a narrowed index width; a separate
   module because a test's name is its main's module name. *)
module ArrInit32
#lang-pulse
open Pulse

fn main ()
  returns x: FStar.Int32.t
{
  ArrInit.main ()
}
