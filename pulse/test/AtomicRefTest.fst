module AtomicRefTest
#lang-pulse
open Pulse
open Pulse.Lib.Atomic
open Pulse.Lib.Atomic.Ref
module U32 = FStar.UInt32

(* An atomic local variable, used through an [atomic_ref]. *)
fn local_counter ()
  returns x: U32.t
  ensures pure (x == 3ul)
{
  let mut c : atomic_t U32.t = to_atomic 1ul;
  to_atomic_ref_pts_to c;
  let _ = fetch_add (of_ref c) 2ul;
  let x = load (of_ref c);
  of_atomic_ref_pts_to c;
  x
}
