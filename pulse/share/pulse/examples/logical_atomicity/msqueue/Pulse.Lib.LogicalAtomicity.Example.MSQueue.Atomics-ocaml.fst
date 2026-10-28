module Pulse.Lib.LogicalAtomicity.Example.MSQueue.Atomics
#lang-pulse

(**
Verified contracts with OCaml-specific external realizations.

The bodies are checked against Atomics.fsti using the existing box API.
Custard extern annotations select MSQueue_atomics.ml at extraction time;
they do not verify that handwritten OCaml implementation. Keeping this
boundary explicit prevents mistaking successful F* verification for a
proof that ordinary mutable OCaml refs implement concurrent CAS.

The selected backend serializes individual primitives with a mutex and
supports spurious-failure injection for regression coverage. It preserves
interleaving between queue steps but provides no lock-free execution claim.
*)

open Pulse.Lib.Pervasives
module B = Pulse.Lib.Box
module U32 = FStar.UInt32

(** Verify the standard load contract; emit a call to the synchronized
native load instead of extracting this body as the runtime implementation. *)
[@@custard_extern "MSQueue_atomics.read"]
atomic fn read (r:B.box U32.t) (#n:erased U32.t) (#p:perm)
  preserves B.pts_to r #p n
  returns value:U32.t
  ensures pure (value == reveal n)
{
  read_atomic_box r
}

(** Verify the standard weak-CAS contract; emit one synchronized comparison
and conditional write, with failure allowed even when values match. *)
[@@custard_extern "MSQueue_atomics.cas"]
atomic fn cas (r:B.box U32.t) (expected desired:U32.t) (#n:erased U32.t)
  requires B.pts_to r n
  returns ok:bool
  ensures cond ok (B.pts_to r desired ** pure (reveal n == expected)) (B.pts_to r n)
{
  cas_box r expected desired
}
