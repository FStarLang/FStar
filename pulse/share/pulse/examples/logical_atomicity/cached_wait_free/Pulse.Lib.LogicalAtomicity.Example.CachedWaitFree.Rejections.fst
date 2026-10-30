module Pulse.Lib.LogicalAtomicity.Example.CachedWaitFree.Rejections
#lang-pulse

(** Publication, exclusive cache writing, and completed copying are distinct
capabilities. In particular, publication alone does not justify unmarking. *)

open Pulse.Lib.Pervasives
module H = Pulse.Lib.LogicalAtomicity.Example.CachedWaitFree.Model
module N = Pulse.Lib.LogicalAtomicity.Example.CachedWaitFree.Storage
module Q = Pulse.Lib.LogicalAtomicity.Example.CachedWaitFree.State
module V = Pulse.Lib.LogicalAtomicity.Example.CachedWaitFree.Validate
module P = Pulse.Lib.LogicalAtomicity.Example.CachedWaitFree.Registry
module G = Pulse.Lib.GhostReference

[@@expect_failure [228]]
fn premature_unmark (#cells:N.arena) (q:Q.big_atomic cells) ver (node:N.id cells)
  preserves Q.shared q
  requires V.published q ver node
{
  V.unmark q node
}

[@@expect_failure [228]]
fn write_without_lock (#cells:N.arena) (q:Q.big_atomic cells) ver (node:N.id cells)
  preserves Q.shared q
  requires V.published q ver node
{
  V.write_word q (ver + 1) node true (N.value cells node)
}

[@@expect_failure [228]]
ghost fn duplicate_writer (#cells:N.arena) (q:Q.big_atomic cells) ver node (cache:H.value)
  requires V.held q ver node cache
  ensures V.held q ver node cache ** V.held q ver node cache
{}

fn completed_copy_may_unmark (#cells:N.arena) (q:Q.big_atomic cells) (node:N.id cells)
  preserves Q.shared q
  requires V.released q node
{
  V.unmark q node
}

[@@expect_failure [228]]
ghost fn duplicate_request_token (r:P.request)
  requires G.pts_to r.P.token ()
  ensures G.pts_to r.P.token () ** G.pts_to r.P.token ()
{}

[@@expect_failure [228]]
ghost fn collect_twice (cells:N.arena) g outer
  (nodes:FStar.Seq.seq (N.id cells) { 0 < FStar.Seq.length nodes })
  (e:P.entry { e.P.observed =!= FStar.Seq.index nodes (FStar.Seq.length nodes - 1) })
  requires P.entry_body cells g outer nodes e ** G.pts_to e.P.req.P.token ()
{
  P.collect cells g outer nodes e;
  P.collect cells g outer nodes e;
}

[@@expect_failure [228]]
let cannot_send_caller_completion caller (marker:G.ref nat) :
  is_send (loc caller ** G.pts_to marker 0) =
  FStar.Tactics.Typeclasses.solve
