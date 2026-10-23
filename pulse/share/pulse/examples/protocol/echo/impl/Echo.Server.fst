module Echo.Server

#lang-pulse

(**
  C entry points.  Each serves one fresh connection (empty byte history)
  until the peer closes or sends a malformed frame, then closes it and
  returns an [echo_report].

    * [echo_session_direct]   -- hand-written loop over [Pulse.Lib.BufferedTCP]
                                 scheduled by the Layer-1 classifier
                                 ([Echo.Server.Direct.serve_direct]);
    * [echo_session_endpoint] -- the Layer-2 [buffered_stream_endpoint] driven
                                 by [drive_until_conclusive]
                                 ([Echo.Server.Endpoint.serve_endpoint]).

  The functional-correctness statements are the postconditions of
  [serve_direct] / [serve_endpoint]: at every point the bytes sent equal the
  bytes consumed, which are a sequence of well-formed frames
  ([Echo.Spec.echo_inv]).  The sessions close the channel, so their own
  postcondition is [emp].
**)

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module Seq = FStar.Seq
module SZ  = FStar.SizeT
module TCP = Pulse.Lib.TCP
module BT  = Pulse.Lib.BufferedTCP

open Echo.Spec
open Echo.Report
open Echo.Step
open Echo.Server.Direct
open Echo.Server.Endpoint

(** The receive buffer is heap-allocated by [BT.wrap_empty] (and freed by
    [BT.close]); the echo buffer lives on the stack. *)
divergent fn echo_session_direct (ch:TCP.channel)
  requires
    TCP.is_channel ch 'r 's **
    pure (Seq.length 'r == 0 /\ Seq.length 's == 0)
  returns r:echo_report
  ensures emp
{
  let b = BT.wrap_empty ch recv_capacity;
  let mut out = [| 0uy; out_capacity |];
  lemma_echo_inv_empty 'r 's;
  let r = serve_direct b out;
  BT.close b;
  r
}

(** [fuel] bounds the number of reads spent waiting for any single frame. *)
divergent fn echo_session_endpoint (ch:TCP.channel) (fuel:SZ.t)
  requires
    TCP.is_channel ch 'r 's **
    pure (Seq.length 'r == 0 /\ Seq.length 's == 0)
  returns r:echo_report
  ensures emp
{
  let b = BT.wrap_empty ch recv_capacity;
  let mut out = [| 0uy; out_capacity |];
  let mut eof = false;
  lemma_echo_inv_empty 'r 's;
  let e = { ep_buf = b; ep_out = out; ep_eof = eof };
  rewrite each b as e.ep_buf, out as e.ep_out, eof as e.ep_eof;
  fold (owns e () 'r 'r _);
  let r = serve_endpoint e fuel;
  unfold owns;
  BT.close e.ep_buf;
  rewrite each e.ep_out as out, e.ep_eof as eof;
  r
}
