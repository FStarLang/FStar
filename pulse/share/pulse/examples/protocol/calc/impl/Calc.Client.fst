module Calc.Client

#lang-pulse

(**
  Calculator client: the client-side mirror of `Calc.Server`.

  The client drives the protocol. It *issues* a request (writing its wire bytes,
  moving from Idle to Awaiting), and later *processes* the response it receives
  (verifying it matches the prediction, moving back to Idle). Together these two
  entry points implement the small client state machine, with a full layered-log
  correspondence between the bytes the client sent/received, the request/response
  messages, and the abstract state transitions.

  Response prediction reuses the verified server end to end: the client embeds a
  `server_state` and calls `Calc.Server.process_request` to advance it.
**)

module U8 = FStar.UInt8
module SZ = FStar.SizeT
module Seq = FStar.Seq
module G = FStar.Ghost

open Pulse.Lib.Pervasives
module Vec = Pulse.Lib.Vec

open Calc.Wire
open Calc.Log
open Calc.Impl.Types
open Calc.Client.Log
open Calc.Client.Types
module CalcP = Calc.Protocol

(** Copy the 5 request bytes from `src` into `dst`. **)
fn copy5 (dst: Vec.vec U8.t) (src: Vec.vec U8.t)
  requires
    Vec.pts_to dst 'db **
    Vec.pts_to src 'sb **
    pure (Seq.length 'db == 5 /\ Seq.length 'sb == 5)
  ensures
    Vec.pts_to dst 'sb **
    Vec.pts_to src 'sb
{
  let b0 = Vec.op_Dot_Lparen_Rparen src 0sz;
  let b1 = Vec.op_Dot_Lparen_Rparen src 1sz;
  let b2 = Vec.op_Dot_Lparen_Rparen src 2sz;
  let b3 = Vec.op_Dot_Lparen_Rparen src 3sz;
  let b4 = Vec.op_Dot_Lparen_Rparen src 4sz;
  Vec.op_Dot_Lparen_Rparen_Less_Minus dst 0sz b0;
  Vec.op_Dot_Lparen_Rparen_Less_Minus dst 1sz b1;
  Vec.op_Dot_Lparen_Rparen_Less_Minus dst 2sz b2;
  Vec.op_Dot_Lparen_Rparen_Less_Minus dst 3sz b3;
  Vec.op_Dot_Lparen_Rparen_Less_Minus dst 4sz b4;
  with db1. assert (Vec.pts_to dst db1);
  Seq.lemma_eq_elim db1 'sb;
  rewrite (Vec.pts_to dst db1) as (Vec.pts_to dst 'sb)
}

(** Create a new client with an empty predicted server and no pending request. **)
fn new_client ()
  requires emp
  returns c: client_state
  ensures client_exactly c initial_client
{
  let predicted = Calc.Server.new_server ();
  let pending = Vec.alloc 0uy 5sz;
  let c = { predicted; pending };

  rewrite (server_exactly predicted initial_log)
       as (server_exactly c.predicted initial_client.completed);
  with pend. rewrite (Vec.pts_to pending pend) as (Vec.pts_to c.pending pend);

  fold (client_exactly c initial_client);
  c
}

(**
  Issue a request. Requires the client to be Idle; the request bytes must be a
  well-formed request frame. Moves the client to Awaiting, recording the request
  in the sent-bytes stream.
**)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 40"
fn issue_request
  (c: client_state)
  (req_buf: Vec.vec U8.t)
  (#st: erased client_state_abs)
requires
  client_exactly c st **
  Vec.pts_to req_buf 'req_bytes **
  pure (
    None? (G.reveal st).pending /\
    Seq.length 'req_bytes == 5 /\
    parse_request 'req_bytes <> None
  )
ensures exists* (st1: client_state_abs).
  client_exactly c st1 **
  Vec.pts_to req_buf 'req_bytes **
  pure (
    Some? st1.pending /\
    client_single_step (G.reveal st) st1 /\
    client_consistent st1 /\
    client_wire_correspondence st1 /\
    client_sent_bytes st1 `Seq.equal` Seq.append (client_sent_bytes (G.reveal st)) 'req_bytes /\
    client_recv_bytes st1 `Seq.equal` client_recv_bytes (G.reveal st)
  )
{
  unfold (client_exactly c st);
  copy5 c.pending req_buf;

  lemma_client_issue_correspondence 'req_bytes (G.reveal st);
  lemma_client_issue_single_step 'req_bytes (G.reveal st);

  rewrite (server_exactly c.predicted (G.reveal st).completed)
       as (server_exactly c.predicted (client_issue 'req_bytes (G.reveal st)).completed);
  fold (client_exactly c (client_issue 'req_bytes (G.reveal st)))
}
#pop-options

(**
  Process a received response. Requires the client to be Awaiting, and the
  received bytes to match the response predicted by the calculator semantics for
  the outstanding request. Moves the client back to Idle, recording the response
  in the received-bytes stream and advancing the predicted state.
**)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 100"
fn process_response
  (c: client_state)
  (resp_buf: Vec.vec U8.t)
  (#st: erased client_state_abs)
requires
  client_exactly c st **
  Vec.pts_to resp_buf 'resp_bytes **
  pure (
    Some? (G.reveal st).pending /\
    Seq.length 'resp_bytes == 5 /\
    (CalcP.calc_frame_response_for (G.reveal st).completed (Some?.v (G.reveal st).pending)
       `Seq.equal` 'resp_bytes)
  )
ensures exists* (st1: client_state_abs).
  client_exactly c st1 **
  Vec.pts_to resp_buf 'resp_bytes **
  pure (
    None? st1.pending /\
    client_single_step (G.reveal st) st1 /\
    client_recv_step_ok (G.reveal st) st1 'resp_bytes /\
    client_consistent st1 /\
    client_wire_correspondence st1 /\
    client_sent_bytes st1 `Seq.equal` client_sent_bytes (G.reveal st) /\
    client_recv_bytes st1 `Seq.equal` Seq.append (client_recv_bytes (G.reveal st)) 'resp_bytes
  )
{
  unfold (client_exactly c st);
  with pend. assert (Vec.pts_to c.pending pend);
  assert (pure (pend == Some?.v (G.reveal st).pending));

  let scratch = Vec.alloc 0uy 5sz;
  Calc.Server.process_request c.predicted c.pending scratch;
  with resp_bytes1 log1. _;
  Vec.free scratch;

  // The response the server actually produced equals the received bytes.
  Seq.lemma_eq_elim (CalcP.calc_frame_response_for (G.reveal st).completed pend) resp_bytes1;
  Seq.lemma_eq_elim (CalcP.calc_frame_response_for (G.reveal st).completed pend) 'resp_bytes;
  assert (pure (resp_bytes1 == Ghost.reveal 'resp_bytes));

  // The received response satisfies the client network step for the received bytes.
  assert (pure (CalcP.calc_frame_network_step_ok
                  (G.reveal st).completed pend (G.reveal log1) 'resp_bytes));

  // Extract log_consistent log1 (gives the client-side correspondence facts).
  unfold (server_exactly c.predicted (G.reveal log1));
  with sb ss. assert (pure (log_consistent (G.reveal log1)));
  fold (server_exactly c.predicted (G.reveal log1));

  // Discharge the pure postcondition for the concrete resulting abstract state.
  assert (pure (client_recv_step_ok (G.reveal st)
                  ({ completed = G.reveal log1; pending = None }) 'resp_bytes));
  assert (pure (client_single_step (G.reveal st)
                  ({ completed = G.reveal log1; pending = None })));
  assert (pure (client_consistent ({ completed = G.reveal log1; pending = None })));
  assert (pure (client_wire_correspondence ({ completed = G.reveal log1; pending = None })));
  assert (pure (client_sent_bytes ({ completed = G.reveal log1; pending = None })
                  `Seq.equal` client_sent_bytes (G.reveal st)));
  assert (pure (client_recv_bytes ({ completed = G.reveal log1; pending = None })
                  `Seq.equal` Seq.append (client_recv_bytes (G.reveal st)) 'resp_bytes));

  rewrite (server_exactly c.predicted (G.reveal log1))
       as (server_exactly c.predicted
             ({ completed = G.reveal log1; pending = None }).completed);
  fold (client_exactly c ({ completed = G.reveal log1; pending = None }))
}
#pop-options
