module Pulse.Lib.LogicalAtomicity.Example.MSQueue.Atomics
#lang-pulse

(**
Semantic implementation of the queue's atomic wrapper API.

Each body delegates to an existing verified Pulse box primitive with the
same resource contract. This file establishes the wrapper at the model
level; it is not the selected native concurrent realization. In particular,
a verified primitive specification alone does not make an arbitrary
read/compare/write target lowering safe under OCaml domain interleavings.
See Atomics-ocaml.fst and MSQueue_atomics.ml for that separate trust boundary.
*)

open Pulse.Lib.Pervasives
module B = Pulse.Lib.Box
module U32 = FStar.UInt32

(** Reuse the primitive's exact-value, fraction-preserving load rule. *)
atomic fn read (r:B.box U32.t) (#n:erased U32.t) (#p:perm)
  preserves B.pts_to r #p n
  returns value:U32.t
  ensures pure (value == reveal n)
{
  read_atomic_box r
}

(** Reuse the primitive CAS rule, including its permitted spurious failure.
No stronger failure implication is introduced by this wrapper. *)
atomic fn cas (r:B.box U32.t) (expected desired:U32.t) (#n:erased U32.t)
  requires B.pts_to r n
  returns ok:bool
  ensures cond ok (B.pts_to r desired ** pure (reveal n == expected)) (B.pts_to r n)
{
  cas_box r expected desired
}
