module Echo.Server.Endpoint

#lang-pulse

(**
  The echo server as a Layer-2 relational endpoint
  ([Pulse.Lib.BufferedStream.buffered_stream_endpoint]), driven by the
  generic [Pulse.Lib.BufferedStream.drive_until_conclusive] loop.

    * [owns e () received committed model] is the endpoint's exclusive
      ownership: the buffered channel ([BT.is_buffered]), the echo buffer and
      an end-of-stream flag, together with [Echo.Spec.echo_inv]
      (sent == committed, committed is a sequence of well-formed frames).
    * [process] runs [Echo.Step.echo_step] on the exact pending bytes: a
      complete frame is echoed and committed ([Yield]); a malformed header is
      [Reject Malformed]; an incomplete frame is [NeedMore] -- unless the
      previous read hit end-of-stream, in which case it is
      [Reject PeerClosed].
    * [read] (only reachable after [NeedMore], via [read_auth]) calls
      [BT.read_more] and records a 0-byte read in the end-of-stream flag.

  [serve_endpoint] repeatedly calls [drive_until_conclusive]; each call
  returns after one echoed frame or a terminal decision.
**)

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module Seq = FStar.Seq
module SZ  = FStar.SizeT
module U8  = FStar.UInt8
module U64 = FStar.UInt64
module TCP = Pulse.Lib.TCP
module BT  = Pulse.Lib.BufferedTCP
module BS  = Pulse.Lib.BufferedStream

open Pulse.Lib.BufferedStream.Classifier
open Echo.Spec
open Echo.Report
open Echo.Step

noeq
type endpoint = {
  ep_buf: BT.t;
  ep_out: array U8.t;
  ep_eof: ref bool;
}

(** Results are the classifier decisions themselves. *)
type result = classification SZ.t echo_error

noextract
let decide (r:result) : GTot (classification SZ.t echo_error) = r

noextract
let ep_needs_more (st:unit) (pending:bytes) : prop =
  needs_more echo_sp st pending

noextract
let result_valid (_:endpoint) (_before:unit) (r:result) (_after:unit) : prop =
  match r with
  | Yield k n ->
    SZ.v k == header_len + SZ.v n /\ 1 <= SZ.v n /\ SZ.v n <= max_payload
  | Progress _ -> False
  | _ -> True

noextract
let owns
  (e:endpoint)
  (_:unit)
  (received committed:bytes)
  (model:BT.phys_buffer)
  : slprop =
  exists* sent ob eof.
    BT.is_buffered e.ep_buf model received committed sent **
    pts_to e.ep_out ob **
    pts_to e.ep_eof eof **
    pure (
      Seq.length ob == SZ.v out_capacity /\
      echo_inv committed sent /\
      BT.capacity model >= max_frame)

noextract
let terminal (e:endpoint) (st:unit) (received:bytes) : slprop =
  exists* committed model. owns e st received committed model

noextract
let buffer_full (e:endpoint) (st:unit) (received:bytes) : slprop =
  exists* committed model. owns e st received committed model

noextract
let read_auth
  (e:endpoint)
  (st:unit)
  (received committed:bytes)
  (model:BT.phys_buffer)
  : slprop =
  owns e st received committed model **
  pure (ep_needs_more st (BT.pending model))

(* ------------------------------------------------------------------ *)
(* Endpoint operations                                                *)
(* ------------------------------------------------------------------ *)

ghost
fn owns_wf
  (e:endpoint)
  (st:Ghost.erased unit)
  (received committed:Ghost.erased bytes)
  (model:Ghost.erased BT.phys_buffer)
  requires owns e st received committed model
  ensures
    owns e st received committed model **
    pure (
      BT.buffer_wf model /\
      BT.received_split received committed model)
{
  unfold owns;
  BT.recall_model e.ep_buf;
  fold (owns e st received committed model)
}

let lemma_can_read (model:BT.phys_buffer)
  : Lemma
      (requires
        BT.buffer_wf model /\
        BT.capacity model >= max_frame /\
        needs_more echo_sp () (BT.pending model))
      (ensures BT.can_read model)
= lemma_needmore_short (BT.pending model)

let lemma_yield_transition
  (e:endpoint)
  (k l:SZ.t)
  (committed committed':bytes)
  (model model':BT.phys_buffer)
  : Lemma
      (requires
        classify () (BT.pending model) == Yield k l /\
        SZ.v k <= Seq.length (BT.pending model) /\
        (committed', model') == step_commit echo_sp () committed model)
      (ensures
        BS.process_transition
          (Yield k l <: classification SZ.t echo_error)
          committed committed' model model' /\
        result_valid e () (Yield k l) ())
= ()

let lemma_read_delivers
  (received:bytes)
  (model model':BT.phys_buffer)
  (chunk:bytes)
  : Lemma
      (requires
        BT.buffer_wf model' /\
        BT.capacity model' == BT.capacity model /\
        BT.chunk_fits model chunk /\
        Seq.equal (BT.pending model') (Seq.append (BT.pending model) chunk))
      (ensures
        BS.read_delivers received (Seq.append received chunk) model model')
= introduce exists (c:bytes).
      BT.chunk_fits model c /\
      Seq.equal (BT.pending model') (Seq.append (BT.pending model) c) /\
      Seq.equal (Seq.append received chunk) (Seq.append received c)
  with chunk and ()

#push-options "--z3rlimit 10"
fn process
  (e:endpoint)
  (st:Ghost.erased unit)
  (received committed:Ghost.erased bytes)
  (model:Ghost.erased BT.phys_buffer)
  requires owns e st received committed model
  returns outcome:BS.process_outcome SZ.t echo_error result
  ensures
    BS.process_post
      decide ep_needs_more result_valid owns terminal buffer_full read_auth
      e st received committed model outcome
{
  unfold owns;
  BT.recall_model e.ep_buf;
  let d = echo_step e.ep_buf e.ep_out;
  with model' committed' sent' ob'.
    assert (BT.is_buffered e.ep_buf model' received committed' sent' **
            pts_to e.ep_out ob');
  match d {
    Yield k l -> {
      lemma_yield_transition e k l committed committed' model model';
      fold (owns e st received committed' model');
      fold (BS.process_post
        decide ep_needs_more result_valid owns terminal buffer_full read_auth
        e st received committed model
        (BS.Processed (Yield k l) (Yield k l)));
      BS.Processed (Yield k l) (Yield k l)
    }
    NeedMore -> {
      let eof = !e.ep_eof;
      if eof {
        // The last read returned no bytes and the frame is still incomplete.
        fold (owns e st received committed' model');
        fold (terminal e st received);
        fold (BS.process_post
          decide ep_needs_more result_valid owns terminal buffer_full read_auth
          e st received committed model
          (BS.Processed (Reject PeerClosed) (Reject PeerClosed)));
        BS.Processed (Reject PeerClosed) (Reject PeerClosed)
      } else {
        lemma_can_read model;
        fold (owns e st received committed' model');
        fold (read_auth e st received committed' model');
        fold (BS.process_post
          decide ep_needs_more result_valid owns terminal buffer_full read_auth
          e st received committed model
          (BS.Processed NeedMore NeedMore));
        BS.Processed NeedMore NeedMore
      }
    }
    Reject err -> {
      fold (owns e st received committed' model');
      fold (terminal e st received);
      fold (BS.process_post
        decide ep_needs_more result_valid owns terminal buffer_full read_auth
        e st received committed model
        (BS.Processed (Reject err) (Reject err)));
      BS.Processed (Reject err) (Reject err)
    }
    Progress _ -> {
      unreachable ()
    }
  }
}
#pop-options

fn read
  (e:endpoint)
  (st:Ghost.erased unit)
  (received committed:Ghost.erased bytes)
  (model:Ghost.erased BT.phys_buffer)
  requires
    read_auth e st received committed model **
    pure (
      BT.buffer_wf model /\
      BT.can_read model /\
      ep_needs_more st (BT.pending model))
  ensures
    exists* received' model'.
      owns e st received' committed model' **
      pure (BS.read_delivers received received' model model')
{
  unfold read_auth;
  unfold owns;
  let n = BT.read_more e.ep_buf;
  with chunk model'.
    assert (BT.is_buffered e.ep_buf model' (Seq.append received chunk) committed _);
  if (n = 0sz) {
    e.ep_eof := true;
  };
  lemma_read_delivers received model model' chunk;
  fold (owns e st (Seq.append received chunk) committed model')
}

noextract
unfold
let echo_endpoint
  : BS.buffered_stream_endpoint endpoint unit SZ.t echo_error result
= {
  BS.bse_decide = decide;
  BS.bse_needs_more = ep_needs_more;
  BS.bse_result_valid = result_valid;
  BS.bse_owns = owns;
  BS.bse_terminal = terminal;
  BS.bse_buffer_full = buffer_full;
  BS.bse_read_auth = read_auth;
  BS.bse_owns_wf = owns_wf;
  BS.bse_process = process;
  BS.bse_read = read;
}

(* ------------------------------------------------------------------ *)
(* The server loop                                                    *)
(* ------------------------------------------------------------------ *)

noextract inline_for_extraction
let incr_frames (n:U64.t) : U64.t =
  if U64.lt n 0xffffffffffffffffUL then U64.add n 1UL else n

noextract inline_for_extraction
let status_of_error (err:echo_error) : echo_status =
  match err with
  | Malformed -> EchoMalformed
  | PeerClosed -> EchoClosed

(** Echo frames until a terminal decision. [fuel] bounds the number of reads
    spent waiting for any single frame. On return the endpoint still owns the
    connection, with [echo_inv] (see [owns]) intact. *)
#push-options "--z3rlimit 10"
divergent fn serve_endpoint
  (e:endpoint)
  (fuel:SZ.t)
  (#received #committed:erased bytes)
  (#model:erased BT.phys_buffer)
  requires owns e () received committed model
  returns r:echo_report
  ensures exists* received' committed' model'.
    owns e () received' committed' model'
{
  let mut frames = 0UL;
  let mut go = true;
  let mut status = EchoClosed;
  while (!go)
    invariant exists* vgo vframes vstatus received1 committed1 model1.
      pts_to go vgo **
      pts_to frames vframes **
      pts_to status vstatus **
      owns e () received1 committed1 model1
  {
    with received1 committed1 model1.
      assert (owns e () received1 committed1 model1);
    rewrite (owns e () received1 committed1 model1)
         as (echo_endpoint.BS.bse_owns e () received1 committed1 model1);
    let outcome =
      BS.drive_until_conclusive
        echo_endpoint
        process
        read
        e
        (Ghost.hide ())
        (Ghost.hide received1)
        (Ghost.hide committed1)
        (Ghost.hide model1)
        fuel;
    unfold (BS.drive_post echo_endpoint e () outcome);
    match outcome {
      BS.DriveYield _ _ _ _ -> {
        with st2 received2 committed2 model2.
          assert (echo_endpoint.BS.bse_owns e st2 received2 committed2 model2);
        rewrite (echo_endpoint.BS.bse_owns e st2 received2 committed2 model2)
             as (owns e () received2 committed2 model2);
        let n = !frames;
        frames := incr_frames n;
      }
      BS.DriveProgress _ _ _ -> {
        // [result_valid] rules out Progress results.
        unreachable ()
      }
      BS.DriveReject _ err _ -> {
        with st2 received2.
          assert (echo_endpoint.BS.bse_terminal e st2 received2);
        rewrite (echo_endpoint.BS.bse_terminal e st2 received2)
             as (terminal e () received2);
        unfold terminal;
        go := false;
        status := status_of_error err;
      }
      BS.DriveBufferFull _ _ -> {
        with st2 received2.
          assert (echo_endpoint.BS.bse_buffer_full e st2 received2);
        rewrite (echo_endpoint.BS.bse_buffer_full e st2 received2)
             as (buffer_full e () received2);
        unfold buffer_full;
        go := false;
        status := EchoBufferFull;
      }
      BS.DriveExhausted -> {
        with st2 received2 committed2 model2.
          assert (echo_endpoint.BS.bse_owns e st2 received2 committed2 model2);
        rewrite (echo_endpoint.BS.bse_owns e st2 received2 committed2 model2)
             as (owns e () received2 committed2 model2);
        go := false;
        status := EchoOutOfFuel;
      }
    }
  };
  let n = !frames;
  let st = !status;
  ({ frames = n; status = st })
}
#pop-options
