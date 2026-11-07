module Pulse.Lib.LogicalAtomicity.Example.ConcurrentSet.Rejections
#lang-pulse

(**
Misuse regressions for the set and its client protocol.

These definitions must fail verification; they are not admitted code.
The positive counterparts are State.advance, Concurrent.produce_range,
Concurrent.consume_twice, and Concurrent.remove_again. Inspect diagnostics
with --print_expected_failures to ensure failures concern the intended resources.
*)

open Pulse.Lib.Pervasives
module H = Pulse.Lib.LogicalAtomicity.Example.ConcurrentSet.Model
module N = Pulse.Lib.LogicalAtomicity.Example.ConcurrentSet.Storage
module Q = Pulse.Lib.LogicalAtomicity.Example.ConcurrentSet.State
module C = Pulse.Lib.LogicalAtomicity.Example.ConcurrentSet.Concurrent

(** Without the predecessor lock, a successor observation no longer pins a node. *)
[@@expect_failure [228]]
divergent fn advance_after_unlock (q:Q.set) (p:Q.node q)
  (c:nat { p < c /\ c < Q.capacity q + 1 })
  preserves Q.is_set q
  requires N.held (N.at q.Q.cells p) c
{
  Q.unlock q p;
  let _ = Q.advance q p c;
  ()
}

(** The producer's private cursor forbids inserting the same key twice. *)
[@@expect_failure [228]]
divergent fn repeat_production (c:C.client { C.well_named c }) (k:Q.key c.C.set)
  preserves C.valid c
  requires C.producer c.C.produced (k - 1)
{
  let _ = C.produce c k;
  let _ = C.produce c k;
  ()
}

(** A FAILED removal gives no tombstone: a future producer may still add k. *)
[@@expect_failure [19]]
divergent fn failed_remove_is_stable (c:C.client { C.well_named c }) (k:Q.key c.C.set)
  (#d:erased (Q.contents c.C.set.Q.cells))
  preserves C.valid c
  requires C.consumer c.C.removed d
{
  let first = C.try_remove c k;
  unfold C.consumed_post;
  if (not first) {
    let _ = C.remove_again c k;
    ()
  } else { () }
}
