module Pulse.Lib.LogicalAtomicity.Example.MSQueue.Atomics
#lang-pulse

(**
Explicit atomic-primitive boundary for the queue example.

Both F* implementations verify these contracts using the UInt32
`Pulse.Lib.Atomic` box operations; no pointer-CAS axiom or new checker rule
is introduced. The -model.fst is for semantic verification. The -ocaml.fst
selects handwritten externals (MSQueue_atomics.ml, over OCaml `Atomic.t`)
so concurrent runtime tests can inject spurious CAS failures.

The OCaml realization is lock-free: reads are `Atomic.get` and CAS is a
structural-compare/`Atomic.compare_and_set` retry loop. It is a trusted
test realization, not a verified OCaml implementation. CAS failure may be
spurious, and all queue retry proofs must tolerate that possibility.
*)

open Pulse.Lib.Pervasives
module AT = Pulse.Lib.Atomic
module U32 = FStar.UInt32

(** One observable load, preserving the supplied fraction and returning
exactly the owned value. Invariant opening lends that ownership at the step. *)
atomic fn read (r:AT.atomic_box U32.t) (#n:erased U32.t) (#p:perm)
  preserves AT.box_pts_to r #p n
  returns value:U32.t
  ensures pure (value == reveal n)

(** Success requires old = expected and writes desired. Failure leaves
the field unchanged but DOES NOT prove old differs from expected. Full
ownership is required; the invariant restores it before another step. *)
atomic fn cas (r:AT.atomic_box U32.t) (expected desired:U32.t) (#n:erased U32.t)
  requires AT.box_pts_to r n
  returns ok:bool
  ensures cond ok (AT.box_pts_to r desired ** pure (reveal n == expected)) (AT.box_pts_to r n)
