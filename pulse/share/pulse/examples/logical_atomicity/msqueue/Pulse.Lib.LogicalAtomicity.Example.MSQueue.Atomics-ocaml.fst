module Pulse.Lib.LogicalAtomicity.Example.MSQueue.Atomics
#lang-pulse

(**
Verified contracts with OCaml-specific external realizations.

The bodies are checked against Atomics.fsti using `Pulse.Lib.Atomic`.
Custard extern annotations select MSQueue_atomics.ml at extraction time;
they do not verify that handwritten OCaml implementation. Keeping this
boundary explicit prevents mistaking successful F* verification for a
proof of the native code.

The selected backend operates directly on OCaml `Atomic.t` cells (the
extracted representation of `AT.atomic_box`) and supports spurious-failure
injection for regression coverage of the queue's retry paths.
*)

open Pulse.Lib.Pervasives
module AT = Pulse.Lib.Atomic
module U32 = FStar.UInt32

(** Verify the standard load contract; emit a call to the native
`Atomic.get`-based load instead of extracting this body. *)
[@@custard_extern "MSQueue_atomics.read"]
atomic fn read (r:AT.atomic_box U32.t) (#n:erased U32.t) (#p:perm)
  preserves AT.box_pts_to r #p n
  returns value:U32.t
  ensures pure (value == reveal n)
{
  AT.load_box r
}

(** Verify the standard weak-CAS contract; emit one native value-comparing
CAS, with failure allowed even when values match. *)
[@@custard_extern "MSQueue_atomics.cas"]
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
