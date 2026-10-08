module TFTP.Impl.Client.CanonicalProtocol

(**

  The TFTP *client* (receiver, RFC 1350) as a verified instance of the
  reliable-delivery (stop-and-wait ARQ) state machine
  `TFTP.Protocol.tftp_client_wfsm`, refining
  `Pulse.Lib.Protocol.Implementation.protocol_implementation`.  This is a
  verified-but-NOT-extracted refinement witness (a `protocol_implementation`
  dictionary is not Low-star).

    * `pi_process_local` drives the sole local event `Client_start` faithfully:
      from the freshly-created (un-started) state (`tcs_filename == None`, status
      cell `0uy`) it is a genuine `StepOk` that installs the filename and moves
      into the "receiving" state (cell `1uy`), emitting nothing; once a filename
      is known it is a sound `IllegalTransition` no-op.

    * `pi_process_network` dispatches on the single datagram in its input buffer:
        - a DATA datagram (opcode 3, `4 <= len <= 516`) while receiving (cell
          `1uy`) is a genuine `StepOk`: it appends the (ghost) payload slice to
          the abstract `tcs_received`, EMITS a single `Msg_ack blk` (four bytes
          written to the output buffer), and — when the block is short (payload
          `< 512`, i.e. `len < 516`) — completes the transfer (cell `2uy`),
          otherwise stays receiving (cell `1uy`);
        - an ERROR datagram (opcode 5, minimal 5-byte form) while receiving is a
          genuine `StepOk` that aborts (cell `3uy`), emitting nothing;
        - everything else is a sound `IllegalTransition` no-op (the "no
          progress" disjunct of `network_error_refines_state_machine`).

  ── How the client discharges `valid_byte_trace` (the crux) ─────────────────

  TFTP DATA is datagram-delimited (payload length is the datagram's length), so
  it is NOT a strong (prefix) parser and the whole-stream greedy `parses_as`
  refinement used by the TFTP *server* (which only consumes the self-delimiting
  ACK/ERROR) is unavailable to a multi-block receiver.  The pure trace machinery
  in `TFTP.Impl.Client.Log` therefore discharges `WFSM.valid_byte_trace` via the
  DATAGRAM (serialize-equality) disjunct — `received` is exactly the
  concatenation of the serializations of the consumed messages — which this
  Pulse shell maintains incrementally: a DATA `WireEvent` grows `received` by the
  consumed datagram (`== tftp_serialize (Msg_data blk pl)`, via
  `Log.lemma_data_input_is_serialize`) and `sent` by the emitted ACK; an ERROR
  `WireEvent` grows only `received`.

  The abstract DATA payload is a GHOST slice `Log.data_payload_of` of the input
  datagram (the receiver need not physically copy it to prove the trace), and the
  ACK is written with four direct byte stores whose layout
  `Log.lemma_ack_prefix_serialize` reconciles with `tftp_serialize (Msg_ack blk)`.
  This mirrors the YMODEM client instance
  `YModem.Impl.Client.CanonicalProtocol` and the TFTP server shell
  `TFTP.Impl.Server.CanonicalProtocol`; the pure reasoning lives in
  `TFTP.Impl.Client.Log`.

**)

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module CPI = Pulse.Lib.Protocol.Implementation
module SM = Pulse.Lib.Protocol.StateMachine
module SZ = FStar.SizeT
module TCP = Pulse.Lib.TCP
module WF = Pulse.Lib.Protocol.WireFormat
module WFSM = Pulse.Lib.Protocol.WireFormatStateMachine
module FT = Pulse.Lib.Protocol.FileTransfer
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module Seq = FStar.Seq
module L = FStar.List.Tot
module MR = Pulse.Lib.MonotonicGhostRef
module RTC = FStar.ReflexiveTransitiveClosure
module Vec = Pulse.Lib.Vec

module TP = TFTP.Protocol
module Log = TFTP.Impl.Client.Log
module Codec = TFTP.Impl.Codec

open TFTP.Wire

#set-options "--fuel 2 --ifuel 2 --z3rlimit 30"

(* ── the receiver implementation handle ───────────────────────────────────────

   A concrete single-cell status vector carrying a FOUR-valued runtime status
   flag (not-yet-started / receiving / completed / aborted — tied to the abstract
   state by `Log.tc_status_flag_ok`), and a monotonic ghost reference tracking the
   client *log* (received / sent bytes and abstract state) under the
   reflexive-transitive-closure preorder of the single-step relation.  Unlike the
   server, the client needs NO `expected` cell: it ACKs whatever block number it
   observes rather than validating an outstanding one. *)
noeq
type tftp_client_impl = {
  status   : Vec.vec U8.t;                        // single cell: 0/1/2/3 status flag
  progress : MR.mref Log.tc_state_ahead_preorder; // ghost history under the RTC preorder
}

(* ── invariant / snapshot ─────────────────────────────────────────────────── *)

let tftp_client_inv
  (i:tftp_client_impl) (received:TCP.bytes) (sent:TCP.bytes) (st:TP.tftp_client_state)
  : slprop =
  (exists* (svs:Seq.seq U8.t).
     Vec.pts_to i.status svs **
     pure (Seq.length svs == 1 /\ Log.tc_status_flag_ok (Seq.index svs 0) st)) **
  MR.pts_to i.progress #1.0R (Log.mk_log received sent st) **
  pure (Log.client_trace_ok received sent (Log.mk_log received sent st))

let tftp_client_snap
  (i:tftp_client_impl) (received:TCP.bytes) (sent:TCP.bytes) (st:TP.tftp_client_state)
  : slprop =
  MR.snapshot i.progress (Log.mk_log received sent st)

(* ── network frame: a 512-byte scratch (max DATA payload), threaded unused
   because the receiver derives the abstract payload from a GHOST slice of the
   datagram and writes the ACK directly to the output buffer.  Mirrors the
   server's `tsnf_buf` / YMODEM's `ycnf_data` for structural parity. *)
noeq
type tftp_client_network_frame = {
  tcnf_buf : array U8.t;   // 512-byte scratch (unused: payload is a ghost slice)
}

let tftp_client_network_frame_pre
  (frame:tftp_client_network_frame)
  (input:array U8.t) (input_len:SZ.t) (out:array U8.t) (out_len:SZ.t)
  (input_contents:TCP.bytes) (old_out:TCP.bytes)
  : slprop =
  (exists* d. pts_to frame.tcnf_buf d ** pure (Seq.length d == 512)) **
  pure (
    SZ.v input_len == Seq.length input_contents /\
    SZ.v out_len >= 4 /\
    Seq.length old_out == SZ.v out_len)

let tftp_client_network_frame_post
  (frame:tftp_client_network_frame)
  (result:CPI.process_result)
  (input_contents:TCP.bytes) (input_len:SZ.t)
  (old_out:TCP.bytes) (out_contents:TCP.bytes)
  (st0:TP.tftp_client_state) (st1:TP.tftp_client_state)
  (consumed:TCP.bytes)
  (wire_outputs:list tftp_message) (local_outputs:list unit)
  : slprop =
  (exists* o'. pts_to frame.tcnf_buf o' ** pure (Seq.length o' == 512)) **
  pure (local_outputs == Log.no_local_outputs)

(* ── local frame: the receiver's sole local event (start) emits no wire message
   and touches no buffer. *)
type tftp_client_local_frame = unit

let tftp_client_local_frame_pre
  (ev:TP.tftp_client_local)
  (frame:tftp_client_local_frame)
  (st0:TP.tftp_client_state)
  (out:array U8.t) (out_len:SZ.t) (old_out:TCP.bytes)
  : slprop = emp

let tftp_client_local_frame_post
  (ev:TP.tftp_client_local)
  (frame:tftp_client_local_frame)
  (result:CPI.process_result)
  (old_out:TCP.bytes) (out_contents:TCP.bytes)
  (st0:TP.tftp_client_state) (st1:TP.tftp_client_state)
  (wire_outputs:list tftp_message) (local_outputs:list unit)
  : slprop = emp

(* ── ghost obligations (port of the server / YMODEM instance) ─────────────── *)

ghost fn tftp_client_invariant_valid
  (i:tftp_client_impl)
  (received:erased TCP.bytes)
  (sent:erased TCP.bytes)
  (st:erased TP.tftp_client_state)
requires tftp_client_inv i received sent st
ensures
  tftp_client_inv i received sent st **
  pure (
    WFSM.valid_byte_trace
      (TP.tftp_client_wfsm)
      (Ghost.reveal received)
      (Ghost.reveal st)
      (Ghost.reveal sent)
      Seq.empty)
{
  unfold (tftp_client_inv i received sent st);
  with svs. _;
  Log.lemma_client_trace_ok_valid received sent (Log.mk_log received sent st);
  fold (tftp_client_inv i received sent st)
}

ghost fn tftp_client_take_snapshot
  (i:tftp_client_impl)
  (received:erased TCP.bytes)
  (sent:erased TCP.bytes)
  (st:erased TP.tftp_client_state)
requires tftp_client_inv i received sent st
ensures
  tftp_client_inv i received sent st **
  tftp_client_snap i received sent st
{
  unfold (tftp_client_inv i received sent st);
  with svs. _;
  MR.take_snapshot i.progress (Log.mk_log received sent st);
  fold (tftp_client_snap i received sent st);
  fold (tftp_client_inv i received sent st)
}

ghost fn tftp_client_recall_snapshot
  (i:tftp_client_impl)
  (snapshot_received:erased TCP.bytes)
  (snapshot_sent:erased TCP.bytes)
  (snapshot_state:erased TP.tftp_client_state)
  (current_received:erased TCP.bytes)
  (current_sent:erased TCP.bytes)
  (current_state:erased TP.tftp_client_state)
requires
  tftp_client_snap i snapshot_received snapshot_sent snapshot_state **
  tftp_client_inv i current_received current_sent current_state
ensures
  tftp_client_snap i snapshot_received snapshot_sent snapshot_state **
  tftp_client_inv i current_received current_sent current_state **
  pure (
    CPI.state_ahead
      (TP.tftp_client_wfsm)
      (Ghost.reveal snapshot_state)
      (Ghost.reveal current_state) /\
    CPI.histories_ahead
      (Ghost.reveal snapshot_received)
      (Ghost.reveal snapshot_sent)
      (Ghost.reveal current_received)
      (Ghost.reveal current_sent))
{
  unfold (tftp_client_snap i snapshot_received snapshot_sent snapshot_state);
  unfold (tftp_client_inv i current_received current_sent current_state);
  with svs. _;
  MR.recall_snapshot i.progress;
  Log.lemma_tc_closure_state_ahead
    (Log.mk_log snapshot_received snapshot_sent snapshot_state)
    (Log.mk_log current_received current_sent current_state);
  Log.lemma_tc_closure_histories_ahead
    (Log.mk_log snapshot_received snapshot_sent snapshot_state)
    (Log.mk_log current_received current_sent current_state);
  fold (tftp_client_snap i snapshot_received snapshot_sent snapshot_state);
  fold (tftp_client_inv i current_received current_sent current_state)
}

(* ── network processing: dispatch on the single datagram ──────────────────── *)

fn tftp_client_process_network
  (i:tftp_client_impl)
  (frame:tftp_client_network_frame)
  (input:array U8.t)
  (input_len:SZ.t)
  (out:array U8.t)
  (out_len:SZ.t)
  (received0:erased TCP.bytes)
  (sent0:erased TCP.bytes)
  (st0:erased TP.tftp_client_state)
  (input_contents:erased TCP.bytes)
  (old_out:erased TCP.bytes)
requires
  tftp_client_inv i received0 sent0 st0 **
  tftp_client_network_frame_pre frame input input_len out out_len input_contents old_out **
  pts_to input input_contents **
  pts_to out old_out **
  pure (CPI.buffers_wf (Ghost.reveal input_contents) input_len (Ghost.reveal old_out) out_len)
returns result:CPI.process_result
ensures exists* (received1:Ghost.erased TCP.bytes)
                (sent1:Ghost.erased TCP.bytes)
                (st1:Ghost.erased TP.tftp_client_state)
                (out_contents:TCP.bytes)
                (consumed:TCP.bytes)
                (wire_outputs:list tftp_message)
                (local_outputs:list unit).
  tftp_client_inv i (Ghost.reveal received1) (Ghost.reveal sent1) (Ghost.reveal st1) **
  tftp_client_network_frame_post
    frame result input_contents input_len old_out out_contents st0 (Ghost.reveal st1)
    consumed wire_outputs local_outputs **
  pts_to input input_contents **
  pts_to out out_contents **
  pure (
    CPI.network_process_correct
      (TP.tftp_client_wfsm)
      (Ghost.reveal input_contents)
      input_len
      (Ghost.reveal old_out)
      out_contents
      out_len
      received0
      sent0
      st0
      result
      (Ghost.reveal received1)
      (Ghost.reveal sent1)
      (Ghost.reveal st1)
      consumed
      wire_outputs
      local_outputs)
{
  unfold (tftp_client_inv i received0 sent0 st0);
  with svs. _;
  let s = Vec.op_Dot_Lparen_Rparen i.status 0sz;
  unfold (tftp_client_network_frame_pre frame input input_len out out_len input_contents old_out);
  with d0. _;
  if (SZ.gte input_len 4sz && SZ.lte input_len 516sz && s = 1uy) {
    let b0 = input.(0sz);
    let b1 = input.(1sz);
    let hd = Codec.u16_hi op_data;
    let ld = Codec.u16_lo op_data;
    if (b0 = hd && b1 = ld) {
      (* DATA datagram: StepOk — append the (ghost) payload, emit an ACK. *)
      let b2 = input.(2sz);
      let b3 = input.(3sz);
      let blk = Codec.u16_of_bytes b2 b3;
      out.(0sz) <- Codec.u16_hi op_ack;
      out.(1sz) <- Codec.u16_lo op_ack;
      out.(2sz) <- Codec.u16_hi blk;
      out.(3sz) <- Codec.u16_lo blk;
      with out_contents. _;
      let pl = Ghost.hide (Log.data_payload_of (Ghost.reveal input_contents) (SZ.v input_len));
      Log.lemma_data_input_is_serialize (Ghost.reveal input_contents) blk (Ghost.reveal pl);
      Log.lemma_data_step (Ghost.reveal st0) blk (Ghost.reveal pl);
      let st1 = Ghost.hide (Log.data_next_state (Ghost.reveal st0) (Ghost.reveal pl));
      let received1 = Ghost.hide (Seq.append (Ghost.reveal received0) (Ghost.reveal input_contents));
      let sent1 = Ghost.hide (Seq.append (Ghost.reveal sent0) (tftp_serialize (Msg_ack blk)));
      let new_flag = (if SZ.lt input_len 516sz then 2uy else 1uy);
      Vec.op_Dot_Lparen_Rparen_Less_Minus i.status 0sz new_flag;
      with svs2. _;
      let log0 = Ghost.hide (Log.mk_log (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st0));
      let log1 = Ghost.hide (Log.mk_log (Ghost.reveal received1) (Ghost.reveal sent1) (Ghost.reveal st1));
      Log.lemma_data_advance (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st0) blk (Ghost.reveal pl);
      RTC.closure_step Log.tc_step_rel (Ghost.reveal log0) (Ghost.reveal log1);
      MR.update i.progress (Ghost.reveal log1);
      fold (tftp_client_inv i (Ghost.reveal received1) (Ghost.reveal sent1) (Ghost.reveal st1));
      Log.lemma_ack_prefix_serialize (Ghost.reveal out_contents) blk;
      Log.lemma_tftp_serialize_all_singleton (Msg_ack blk);
      Log.lemma_network_stepok
        (Ghost.reveal input_contents) input_len (Ghost.reveal old_out) (Ghost.reveal out_contents) out_len
        (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st0)
        (Msg_data blk (Ghost.reveal pl)) (Ghost.reveal st1) 4sz [Msg_ack blk] (tftp_serialize (Msg_ack blk));
      fold (tftp_client_network_frame_post
        frame (Log.tc_result CPI.StepOk input_len 4sz) input_contents input_len old_out (Ghost.reveal out_contents)
        (Ghost.reveal st0) (Ghost.reveal st1) (Ghost.reveal input_contents) [Msg_ack blk] []);
      Log.tc_result CPI.StepOk input_len 4sz
    } else if (input_len = 5sz) {
      let b4 = input.(4sz);
      let he = Codec.u16_hi op_error;
      let le = Codec.u16_lo op_error;
      if (b0 = he && b1 = le && b4 = 0uy) {
        (* ERROR (minimal 5-byte form) while receiving: StepOk — flip to Aborted. *)
        let b2 = input.(2sz);
        let b3 = input.(3sz);
        let code = Codec.u16_of_bytes b2 b3;
        Log.lemma_error_input_is_serialize (Ghost.reveal input_contents) code;
        Log.lemma_error_step (Ghost.reveal st0) code (Seq.empty <: cstring);
        let st1 = Ghost.hide (Log.error_next_state (Ghost.reveal st0));
        let received1 = Ghost.hide (Seq.append (Ghost.reveal received0) (Ghost.reveal input_contents));
        Vec.op_Dot_Lparen_Rparen_Less_Minus i.status 0sz 3uy;
        with svs2. _;
        let log0 = Ghost.hide (Log.mk_log (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st0));
        let log1 = Ghost.hide (Log.mk_log (Ghost.reveal received1) (Ghost.reveal sent0) (Ghost.reveal st1));
        Log.lemma_error_advance (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st0) code;
        RTC.closure_step Log.tc_step_rel (Ghost.reveal log0) (Ghost.reveal log1);
        MR.update i.progress (Ghost.reveal log1);
        fold (tftp_client_inv i (Ghost.reveal received1) (Ghost.reveal sent0) (Ghost.reveal st1));
        Log.lemma_output_written_empty (Ghost.reveal old_out);
        Seq.append_empty_r (Ghost.reveal sent0);
        Log.lemma_network_stepok
          (Ghost.reveal input_contents) input_len (Ghost.reveal old_out) (Ghost.reveal old_out) out_len
          (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st0)
          (Msg_error code (Seq.empty <: cstring)) (Ghost.reveal st1) 0sz [] Seq.empty;
        fold (tftp_client_network_frame_post
          frame (Log.tc_result CPI.StepOk input_len 0sz) input_contents input_len old_out (Ghost.reveal old_out)
          (Ghost.reveal st0) (Ghost.reveal st1) (Ghost.reveal input_contents) [] []);
        Log.tc_result CPI.StepOk input_len 0sz
      } else {
        (* Opcode-5 but not the minimal ERROR: a sound IllegalTransition no-op. *)
        Log.lemma_network_noop
          (Ghost.reveal input_contents) input_len (Ghost.reveal old_out) out_len
          (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st0);
        fold (tftp_client_inv i (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st0));
        fold (tftp_client_network_frame_post
          frame (Log.tc_result CPI.IllegalTransition 0sz 0sz) input_contents input_len old_out (Ghost.reveal old_out)
          (Ghost.reveal st0) (Ghost.reveal st0) Seq.empty [] []);
        Log.tc_result CPI.IllegalTransition 0sz 0sz
      }
    } else {
      (* In range but not DATA and not a 5-byte candidate: a sound no-op. *)
      Log.lemma_network_noop
        (Ghost.reveal input_contents) input_len (Ghost.reveal old_out) out_len
        (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st0);
      fold (tftp_client_inv i (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st0));
      fold (tftp_client_network_frame_post
        frame (Log.tc_result CPI.IllegalTransition 0sz 0sz) input_contents input_len old_out (Ghost.reveal old_out)
        (Ghost.reveal st0) (Ghost.reveal st0) Seq.empty [] []);
      Log.tc_result CPI.IllegalTransition 0sz 0sz
    }
  } else {
    (* Not receiving, or datagram out of range: a sound IllegalTransition no-op. *)
    Log.lemma_network_noop
      (Ghost.reveal input_contents) input_len (Ghost.reveal old_out) out_len
      (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st0);
    fold (tftp_client_inv i (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st0));
    fold (tftp_client_network_frame_post
      frame (Log.tc_result CPI.IllegalTransition 0sz 0sz) input_contents input_len old_out (Ghost.reveal old_out)
      (Ghost.reveal st0) (Ghost.reveal st0) Seq.empty [] []);
    Log.tc_result CPI.IllegalTransition 0sz 0sz
  }
}

(* ── local processing: drive Client_start faithfully ──────────────────────── *)

fn tftp_client_process_local
  (i:tftp_client_impl)
  (ev:TP.tftp_client_local)
  (frame:tftp_client_local_frame)
  (out:array U8.t)
  (out_len:SZ.t)
  (received0:erased TCP.bytes)
  (sent0:erased TCP.bytes)
  (st0:erased TP.tftp_client_state)
  (old_out:erased TCP.bytes)
requires
  tftp_client_inv i received0 sent0 st0 **
  tftp_client_local_frame_pre ev frame st0 out out_len old_out **
  pts_to out old_out **
  pure (
    SZ.v out_len == Seq.length old_out /\
    ~ (CPI.no_internal_events #TP.tftp_client_local ev))
returns result:CPI.process_result
ensures exists* (received1:Ghost.erased TCP.bytes)
                (sent1:Ghost.erased TCP.bytes)
                (st1:Ghost.erased TP.tftp_client_state)
                (out_contents:TCP.bytes)
                (wire_outputs:list tftp_message)
                (local_outputs:list unit).
  tftp_client_inv i (Ghost.reveal received1) (Ghost.reveal sent1) (Ghost.reveal st1) **
  tftp_client_local_frame_post
    ev frame result old_out out_contents st0 (Ghost.reveal st1)
    wire_outputs local_outputs **
  pts_to out out_contents **
  pure (
    CPI.local_process_correct
      (TP.tftp_client_wfsm)
      ev
      old_out
      out_contents
      out_len
      received0
      sent0
      st0
      result
      (Ghost.reveal received1)
      (Ghost.reveal sent1)
      (Ghost.reveal st1)
      wire_outputs
      local_outputs)
{
  unfold (tftp_client_local_frame_pre ev frame st0 out out_len old_out);
  unfold (tftp_client_inv i received0 sent0 st0);
  with svs. _;
  let s = Vec.op_Dot_Lparen_Rparen i.status 0sz;
  match ev {
    TP.Client_start filename -> {
      if (s = 0uy) {
        (* Not-yet-started (filename == None): StepOk — install the filename and
           move into the receiving state (cell 1uy). *)
        Log.lemma_start_step (Ghost.reveal st0) filename;
        let st1 = Ghost.hide (Log.start_next_state filename);
        Vec.op_Dot_Lparen_Rparen_Less_Minus i.status 0sz 1uy;
        with svs2. _;
        let log0 = Ghost.hide (Log.mk_log (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st0));
        let log1 = Ghost.hide (Log.mk_log (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st1));
        Log.lemma_start_advance (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st0) filename;
        RTC.closure_step Log.tc_step_rel (Ghost.reveal log0) (Ghost.reveal log1);
        MR.update i.progress (Ghost.reveal log1);
        fold (tftp_client_inv i (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st1));
        Log.lemma_output_written_empty (Ghost.reveal old_out);
        Seq.append_empty_r (Ghost.reveal sent0);
        Log.lemma_local_stepok ev (Ghost.reveal old_out) (Ghost.reveal old_out) out_len
          (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st0)
          0sz (Ghost.reveal st1) [] Seq.empty;
        fold (tftp_client_local_frame_post ev frame (Log.tc_result CPI.StepOk 0sz 0sz)
          old_out (Ghost.reveal old_out) (Ghost.reveal st0) (Ghost.reveal st1) [] []);
        Log.tc_result CPI.StepOk 0sz 0sz
      } else {
        (* A filename is already known: a sound IllegalTransition no-op. *)
        Log.lemma_local_illegal ev (Ghost.reveal old_out) (Ghost.reveal old_out) out_len
          (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st0);
        fold (tftp_client_inv i (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st0));
        fold (tftp_client_local_frame_post ev frame (Log.tc_result CPI.IllegalTransition 0sz 0sz)
          old_out (Ghost.reveal old_out) (Ghost.reveal st0) (Ghost.reveal st0) [] []);
        Log.tc_result CPI.IllegalTransition 0sz 0sz
      }
    }
  }
}

(* ── constructor: a freshly-created, un-started receiver ──────────────────── *)

fn new_tftp_client ()
requires emp
returns i:tftp_client_impl
ensures tftp_client_inv i Seq.empty Seq.empty TP.tftp_client_initial **
        pure (Vec.is_full_vec i.status)
{
  let status = Vec.alloc 0uy 1sz;
  let progress =
    MR.alloc #_ #Log.tc_state_ahead_preorder
      (Log.mk_log Seq.empty Seq.empty TP.tftp_client_initial);
  let i = { status; progress };
  rewrite (MR.pts_to progress #1.0R (Log.mk_log Seq.empty Seq.empty TP.tftp_client_initial)) as
          (MR.pts_to i.progress #1.0R (Log.mk_log Seq.empty Seq.empty TP.tftp_client_initial));
  with sv. rewrite (Vec.pts_to status sv) as (Vec.pts_to i.status sv);
  Log.lemma_initial_trace_ok ();
  fold (tftp_client_inv i Seq.empty Seq.empty TP.tftp_client_initial);
  assert (pure (Vec.is_full_vec i.status));
  i
}

(* ── the instance ─────────────────────────────────────────────────────────── *)

noextract
let tftp_client_protocol_implementation
  : CPI.protocol_implementation
      tftp_client_impl
      TP.tftp_client_state
      tftp_message
      TP.tftp_client_local
      unit
  =
  {
    CPI.pi_system = (fun _ -> TP.tftp_client_wfsm);
    CPI.pi_internal = CPI.no_internal_events #TP.tftp_client_local;
    CPI.pi_internal_pending = CPI.nothing_pending #TP.tftp_client_state;
    CPI.pi_invariant = tftp_client_inv;
    CPI.pi_snapshot = tftp_client_snap;
    CPI.pi_network_frame = tftp_client_network_frame;
    CPI.pi_network_frame_pre = tftp_client_network_frame_pre;
    CPI.pi_network_frame_post = tftp_client_network_frame_post;
    CPI.pi_local_frame = tftp_client_local_frame;
    CPI.pi_local_frame_pre = tftp_client_local_frame_pre;
    CPI.pi_local_frame_post = tftp_client_local_frame_post;
    CPI.pi_internal_frame_pre =
      CPI.no_internal_frame_pre #tftp_client_local_frame #TP.tftp_client_state;
    CPI.pi_internal_frame_post =
      CPI.no_internal_frame_post #tftp_client_local_frame #TP.tftp_client_state #tftp_message #unit;
    CPI.pi_invariant_valid = tftp_client_invariant_valid;
    CPI.pi_take_snapshot = tftp_client_take_snapshot;
    CPI.pi_recall_snapshot = tftp_client_recall_snapshot;
    CPI.pi_process_network = tftp_client_process_network;
    CPI.pi_process_local = tftp_client_process_local;
    CPI.pi_process_internal =
      CPI.quiescent_process_internal
        #_ #TP.tftp_client_state #tftp_message #TP.tftp_client_local #unit #tftp_client_local_frame
        tftp_client_inv
        (fun _ -> TP.tftp_client_wfsm);
  }
