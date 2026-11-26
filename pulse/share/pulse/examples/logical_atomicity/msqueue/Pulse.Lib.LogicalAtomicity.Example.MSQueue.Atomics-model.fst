module Pulse.Lib.LogicalAtomicity.Example.MSQueue.Atomics
#lang-pulse

(**
Semantic implementation of the queue's atomic wrapper API.

Each body delegates to a `Pulse.Lib.Atomic` box operation. This file
establishes the wrapper at the model level; it is not the selected native
concurrent realization. See Atomics-ocaml.fst and MSQueue_atomics.ml for
that separate trust boundary.
*)

open Pulse.Lib.Pervasives
module AT = Pulse.Lib.Atomic
module U32 = FStar.UInt32

(** Reuse the library's exact-value, fraction-preserving load rule. *)
atomic fn read (r:AT.atomic_box U32.t) (#n:erased U32.t) (#p:perm)
  preserves AT.box_pts_to r #p n
  returns value:U32.t
  ensures pure (value == reveal n)
{
  AT.load_box r
}

(** Weaken the library's strong compare-exchange: its failure-implies-
inequality fact is dropped, so callers must tolerate spurious failure. *)
atomic fn cas (r:AT.atomic_box U32.t) (expected desired:U32.t) (#n:erased U32.t)
  requires AT.box_pts_to r n
  returns ok:bool
  ensures cond ok (AT.box_pts_to r desired ** pure (reveal n == expected)) (AT.box_pts_to r n)
{
  let ok = AT.compare_exchange_box r expected desired;
  if ok {
    intro_cond_true (AT.box_pts_to r desired ** pure (reveal n == expected)) (AT.box_pts_to r n);
    true
  } else {
    intro_cond_false (AT.box_pts_to r desired ** pure (reveal n == expected)) (AT.box_pts_to r n);
    false
  }
}
