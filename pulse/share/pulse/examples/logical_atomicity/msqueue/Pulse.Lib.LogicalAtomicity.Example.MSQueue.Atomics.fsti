module Pulse.Lib.LogicalAtomicity.Example.MSQueue.Atomics
#lang-pulse

(**
Explicit atomic-primitive boundary for the queue example.

Both F* implementations verify these contracts using existing UInt32 box
primitives; no pointer-CAS axiom or new checker rule is introduced. The
-model.fst is for semantic verification. The -ocaml.fst selects handwritten
externals so concurrent runtime tests use indivisible read/CAS rather than
a specification-level read/compare/write lowering.

The OCaml realization uses a mutex around each primitive, not around an
entire queue operation. It is a trusted test realization, not a proof of
native lock-free atomics or a weak-memory implementation. CAS failure may
be spurious, and all queue retry proofs must tolerate that possibility.
*)

open Pulse.Lib.Pervasives
module B = Pulse.Lib.Box
module U32 = FStar.UInt32

(** One observable load, preserving the supplied fraction and returning
exactly the owned value. Invariant opening lends that ownership at the step. *)
atomic fn read (r:B.box U32.t) (#n:erased U32.t) (#p:perm)
  preserves B.pts_to r #p n
  returns value:U32.t
  ensures pure (value == reveal n)

(** Success requires old = expected and writes desired. Failure leaves
the field unchanged but DOES NOT prove old differs from expected. Full
ownership is required; the invariant restores it before another step. *)
atomic fn cas (r:B.box U32.t) (expected desired:U32.t) (#n:erased U32.t)
  requires B.pts_to r n
  returns ok:bool
  ensures cond ok (B.pts_to r desired ** pure (reveal n == expected)) (B.pts_to r n)
