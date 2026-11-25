module Pulse.Lib.LogicalAtomicity.Example.MSQueue.Rejections
#lang-pulse

(**
Negative ownership tests for the FIFO's intrusive-node and payload contracts.

These are expected verification failures, not executable clients or admitted
code. They check that successful enqueue consumes both the one-use node
ticket and its attached payload. Together with the positive Clients proofs,
they distinguish actual ownership transfer from a specification that merely
records numeric values. They do not address reclamation or safe node reuse:
those features are deliberately absent from this example.

When modifying the tests, inspect --print_expected_failures to ensure error
228 reports the intended missing spatial resource rather than an unrelated
failure of the same diagnostic class.
*)

open Pulse.Lib.Pervasives
module B = Pulse.Lib.Box
module S = FStar.Seq
module U32 = FStar.UInt32
module N = Pulse.Lib.LogicalAtomicity.Example.MSQueue.Storage
module Q = Pulse.Lib.LogicalAtomicity.Example.MSQueue.State
module C = Pulse.Lib.LogicalAtomicity.Example.MSQueue.Clients

(** The second enqueue lacks N.ticket cells n. Dequeue would not restore
that ticket either: physical links remain retained for the queue's lifetime. *)
[@@expect_failure [228]]
divergent fn reuse_node (#cells:N.arena) (q:Q.queue cells) (n:N.id cells)
  preserves Q.is_queue q (fun _ -> emp)
  requires Q.model q S.empty ** N.ticket cells n
  ensures exists* xs. Q.model q xs
{
  C.enqueue_owned q (fun _ -> emp) n;
  C.enqueue_owned q (fun _ -> emp) n;
}

(** The queued payload is no longer owned by the caller. It must first be
returned by a successful dequeue before an ordinary boxed read is allowed. *)
[@@expect_failure [228]]
divergent fn read_transferred_payload (#cells:N.arena) (q:Q.queue cells)
  (n:N.id cells) (payload:B.box U32.t)
  preserves Q.is_queue q (fun _ -> B.pts_to payload 7ul)
  requires Q.model q S.empty ** N.ticket cells n ** B.pts_to payload 7ul
  returns value:U32.t
  ensures exists* xs. Q.model q xs
{
  C.enqueue_owned q (fun _ -> B.pts_to payload 7ul) n;
  B.(!payload)
}
