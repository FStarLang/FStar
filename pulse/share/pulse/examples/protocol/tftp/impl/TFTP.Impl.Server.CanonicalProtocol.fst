module TFTP.Impl.Server.CanonicalProtocol

(**

  The TFTP *server* (sender, RFC 1350) as a verified instance of the
  reliable-delivery (ARQ) state machine `TFTP.Protocol.tftp_server_wfsm`,
  refining `Pulse.Lib.Protocol.Implementation.protocol_implementation`.  This is a
  verified-but-NOT-extracted refinement witness (a `protocol_implementation`
  dictionary is not Low-star).

    * `pi_process_local` drives the five local events faithfully:
        - `Server_start`   initialises the transfer (filename/plan), emits
          nothing, sets the status cell to "idle" (0uy);
        - `Server_send`    frames + emits the next DATA block via the verified
          codec leaf `TFTP.Impl.Codec.tftp_emit_data`, records the outstanding
          block number in the `expected` cell, and moves into the
          "one-outstanding" state (1uy);
        - `Server_complete`flips the status to Completed (2uy), emits nothing;
        - `Server_timeout` retransmits the outstanding DATA block when one is in
          flight (cell 1uy), leaving the abstract state unchanged; otherwise a
          sound IllegalTransition no-op;
        - `Server_abort`   flips the status to Aborted (3uy), emits nothing.

    * `pi_process_network` dispatches on the single serialized datagram in its
      input:
        - ACK   (opcode 4) in the one-outstanding state whose block number
          equals the `expected` cell: advance `acked`, emit nothing;
        - ERROR (opcode 5, minimal 5-byte form) while InProgress: flip the
          status to Aborted;
        - everything else: a sound IllegalTransition no-op (the "no progress"
          disjunct of `network_error_refines_state_machine`).

  Unlike YMODEM (1-byte controls), the TFTP server input is an *indexed* 4-byte
  ACK.  The abstract `tftp_server_step` requires the acked block number
  `U16.v blk == tss_acked + 1`, but `tss_acked` is ghost, so the handle carries a
  concrete `expected : Vec.vec U16.t` cell holding the outstanding block number
  while a block is in flight; the invariant couples it to `tss_acked + 1`
  whenever the status cell is 1uy.  The ACK block number is recovered by the
  verified codec leaf `TFTP.Impl.Codec.tftp_recv_ack`.

  The pure ARQ trace / monotonic-log / closure reasoning lives in the
  ordinary-F* helper module `TFTP.Impl.Server.Log`; this module is the thin
  Pulse shell binding the heap resources to it, mirroring the YMODEM server
  instance `YModem.Impl.Server.CanonicalProtocol`.

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
module ID = FStar.IndefiniteDescription
module Vec = Pulse.Lib.Vec

module TP = TFTP.Protocol
module Log = TFTP.Impl.Server.Log
module Codec = TFTP.Impl.Codec

open TFTP.Wire

#set-options "--fuel 2 --ifuel 2 --z3rlimit 30"

(* ── the sender implementation handle ─────────────────────────────────────────

   A concrete single-cell status vector carrying a FOUR-valued runtime status
   flag (idle / one-outstanding / completed / aborted — tied to the abstract
   state by `Log.ts_status_flag_ok`); a single-cell `expected` vector holding the
   outstanding block number while a block is in flight (tied to `tss_acked + 1`
   by the invariant when the status cell is 1uy); and a monotonic ghost reference
   tracking the server *log* (received / sent bytes and abstract state) under the
   reflexive-transitive-closure preorder of the single-step relation. *)
noeq
type tftp_server_impl = {
  status   : Vec.vec U8.t;                        // single cell: 0/1/2/3 status flag
  expected : Vec.vec U16.t;                       // single cell: outstanding block number (valid iff status==1uy)
  progress : MR.mref Log.ts_state_ahead_preorder; // ghost history under the RTC preorder
}

(* ── invariant / snapshot ─────────────────────────────────────────────────── *)

let tftp_server_inv
  (i:tftp_server_impl) (received:TCP.bytes) (sent:TCP.bytes) (st:TP.tftp_server_state)
  : slprop =
  (exists* (svs:Seq.seq U8.t) (evs:Seq.seq U16.t).
     Vec.pts_to i.status svs **
     Vec.pts_to i.expected evs **
     pure (Seq.length svs == 1 /\ Seq.length evs == 1 /\
           Log.ts_status_flag_ok (Seq.index svs 0) st /\
           (Seq.index svs 0 == 1uy ==> U16.v (Seq.index evs 0) == st.TP.tss_acked + 1))) **
  MR.pts_to i.progress #1.0R (Log.mk_log received sent st) **
  pure (Log.server_trace_ok received sent (Log.mk_log received sent st))

let tftp_server_snap
  (i:tftp_server_impl) (received:TCP.bytes) (sent:TCP.bytes) (st:TP.tftp_server_state)
  : slprop =
  MR.snapshot i.progress (Log.mk_log received sent st)

(* ── network frame: a 516-byte scratch (max DATA packet) + block number,
   threaded unused because the server never emits on a network event (ACK/ERROR
   have no wire output).  Mirrors YMODEM's `ysnf_buf` for structural parity. *)
noeq
type tftp_server_network_frame = {
  tsnf_buf : array U8.t;   // 516-byte scratch (unused: network emits nothing)
  tsnf_blk : U16.t;        // block number (unused)
}

let tftp_server_network_frame_pre
  (frame:tftp_server_network_frame)
  (input:array U8.t) (input_len:SZ.t) (out:array U8.t) (out_len:SZ.t)
  (input_contents:TCP.bytes) (old_out:TCP.bytes)
  : slprop =
  (exists* d. pts_to frame.tsnf_buf d ** pure (Seq.length d == 516)) **
  pure (
    SZ.v input_len == Seq.length input_contents /\
    SZ.v out_len >= 516 /\
    Seq.length old_out == SZ.v out_len)

(* Deterministic post-transition witness for the NETWORK handler: every branch
   lands in one of these three (no-op / ack-advance / abort). *)
unfold
let ts_network_post_ok (st0 st1:TP.tftp_server_state) : prop =
  st1 == st0 \/
  st1 == Log.ack_next_state st0 \/
  st1 == Log.abort_next_state st0

let tftp_server_network_frame_post
  (frame:tftp_server_network_frame)
  (result:CPI.process_result)
  (input_contents:TCP.bytes) (input_len:SZ.t)
  (old_out:TCP.bytes) (out_contents:TCP.bytes)
  (st0:TP.tftp_server_state) (st1:TP.tftp_server_state)
  (consumed:TCP.bytes)
  (wire_outputs:list tftp_message) (local_outputs:list unit)
  : slprop =
  (exists* o'. pts_to frame.tsnf_buf o' ** pure (Seq.length o' == 516)) **
  pure (local_outputs == [] /\ ts_network_post_ok st0 st1)

(* ── local frame: the DATA payload buffer + block number + payload length.  Its
   precondition DOES receive `st0`, so it faithfully supplies the outstanding
   block for `Server_send` (== `hd pending`) and `Server_timeout` while one is in
   flight (== `sent[acked]`).  `out` is exactly `4 + tslf_len` bytes (the DATA
   packet size), matching the `tftp_emit_data` codec leaf. *)
noeq
type tftp_server_local_frame = {
  tslf_buf : array U8.t;   // DATA payload
  tslf_blk : U16.t;        // block number
  tslf_len : SZ.t;         // payload length (<= 512)
}

unfold
let local_pre_ok
  (ev:TP.tftp_server_local) (st0:TP.tftp_server_state)
  (d:TCP.bytes) (blk:U16.t) (len:SZ.t) : prop =
  match ev with
  | TP.Server_start filename plan ->
    st0.TP.tss_filename == None /\ TP.plan_wf plan
  | TP.Server_send ->
    Some? st0.TP.tss_filename /\
    st0.TP.tss_status == FT.FT_InProgress /\
    L.length st0.TP.tss_sent == st0.TP.tss_acked /\
    U16.v blk == L.length st0.TP.tss_sent + 1 /\
    Cons? st0.TP.tss_pending /\
    TP.plan_wf st0.TP.tss_pending /\
    Seq.equal (L.hd st0.TP.tss_pending) d /\
    SZ.v len <= 512
  | TP.Server_complete ->
    Some? st0.TP.tss_filename /\
    st0.TP.tss_status == FT.FT_InProgress /\
    st0.TP.tss_pending == [] /\
    st0.TP.tss_acked == L.length st0.TP.tss_sent
  | TP.Server_timeout ->
    st0.TP.tss_status == FT.FT_InProgress /\
    (st0.TP.tss_acked < L.length st0.TP.tss_sent ==>
       U16.v blk == st0.TP.tss_acked + 1 /\
       Seq.equal (L.index st0.TP.tss_sent st0.TP.tss_acked) d /\
       SZ.v len <= 512)
  | TP.Server_abort ->
    st0.TP.tss_status == FT.FT_InProgress

let tftp_server_local_frame_pre
  (ev:TP.tftp_server_local)
  (frame:tftp_server_local_frame)
  (st0:TP.tftp_server_state)
  (out:array U8.t) (out_len:SZ.t) (old_out:TCP.bytes)
  : slprop =
  (exists* (d:Seq.seq U8.t). pts_to frame.tslf_buf d **
     pure (Seq.length d == SZ.v frame.tslf_len /\
           local_pre_ok ev st0 d frame.tslf_blk frame.tslf_len)) **
  pure (Seq.length old_out == 4 + SZ.v frame.tslf_len)

(* Deterministic post-transition witness for the LOCAL handler. *)
unfold
let ts_local_post_ok (ev:TP.tftp_server_local) (st0 st1:TP.tftp_server_state) : prop =
  match ev with
  | TP.Server_start filename plan -> st1 == Log.start_next_state filename plan
  | TP.Server_send -> Cons? st0.TP.tss_pending /\ st1 == Log.send_next_state st0
  | TP.Server_complete -> st1 == Log.complete_next_state st0
  | TP.Server_abort -> st1 == Log.abort_next_state st0
  | TP.Server_timeout -> st1 == st0

let tftp_server_local_frame_post
  (ev:TP.tftp_server_local)
  (frame:tftp_server_local_frame)
  (result:CPI.process_result)
  (old_out:TCP.bytes) (out_contents:TCP.bytes)
  (st0:TP.tftp_server_state) (st1:TP.tftp_server_state)
  (wire_outputs:list tftp_message) (local_outputs:list unit)
  : slprop =
  (exists* (d:Seq.seq U8.t). pts_to frame.tslf_buf d **
     pure (Seq.length d == SZ.v frame.tslf_len)) **
  pure (ts_local_post_ok ev st0 st1)

(* ── ghost obligations (port of the YMODEM instance, re-threading two cells) ── *)

ghost fn tftp_server_invariant_valid
  (i:tftp_server_impl)
  (received:erased TCP.bytes)
  (sent:erased TCP.bytes)
  (st:erased TP.tftp_server_state)
requires tftp_server_inv i received sent st
ensures
  tftp_server_inv i received sent st **
  pure (
    WFSM.valid_byte_trace
      (TP.tftp_server_wfsm)
      (Ghost.reveal received)
      (Ghost.reveal st)
      (Ghost.reveal sent)
      Seq.empty)
{
  unfold (tftp_server_inv i received sent st);
  with svs evs. _;
  Log.lemma_server_trace_ok_valid received sent (Log.mk_log received sent st);
  fold (tftp_server_inv i received sent st)
}

ghost fn tftp_server_take_snapshot
  (i:tftp_server_impl)
  (received:erased TCP.bytes)
  (sent:erased TCP.bytes)
  (st:erased TP.tftp_server_state)
requires tftp_server_inv i received sent st
ensures
  tftp_server_inv i received sent st **
  tftp_server_snap i received sent st
{
  unfold (tftp_server_inv i received sent st);
  with svs evs. _;
  MR.take_snapshot i.progress (Log.mk_log received sent st);
  fold (tftp_server_snap i received sent st);
  fold (tftp_server_inv i received sent st)
}

ghost fn tftp_server_recall_snapshot
  (i:tftp_server_impl)
  (snapshot_received:erased TCP.bytes)
  (snapshot_sent:erased TCP.bytes)
  (snapshot_state:erased TP.tftp_server_state)
  (current_received:erased TCP.bytes)
  (current_sent:erased TCP.bytes)
  (current_state:erased TP.tftp_server_state)
requires
  tftp_server_snap i snapshot_received snapshot_sent snapshot_state **
  tftp_server_inv i current_received current_sent current_state
ensures
  tftp_server_snap i snapshot_received snapshot_sent snapshot_state **
  tftp_server_inv i current_received current_sent current_state **
  pure (
    CPI.state_ahead
      (TP.tftp_server_wfsm)
      (Ghost.reveal snapshot_state)
      (Ghost.reveal current_state) /\
    CPI.histories_ahead
      (Ghost.reveal snapshot_received)
      (Ghost.reveal snapshot_sent)
      (Ghost.reveal current_received)
      (Ghost.reveal current_sent))
{
  unfold (tftp_server_snap i snapshot_received snapshot_sent snapshot_state);
  unfold (tftp_server_inv i current_received current_sent current_state);
  with svs evs. _;
  MR.recall_snapshot i.progress;
  Log.lemma_ts_closure_state_ahead
    (Log.mk_log snapshot_received snapshot_sent snapshot_state)
    (Log.mk_log current_received current_sent current_state);
  Log.lemma_ts_closure_histories_ahead
    (Log.mk_log snapshot_received snapshot_sent snapshot_state)
    (Log.mk_log current_received current_sent current_state);
  fold (tftp_server_snap i snapshot_received snapshot_sent snapshot_state);
  fold (tftp_server_inv i current_received current_sent current_state)
}

(* ── extract the emitted DATA payload from the emit leaf's post ────────────── *)
ghost fn extract_data_payload (d o':erased TCP.bytes) (blk:U16.t)
requires pure (exists (pl:data_payload).
                 (pl <: Seq.seq U8.t) == reveal d /\
                 reveal o' == tftp_serialize (Msg_data blk pl))
returns pl : erased data_payload
ensures pure ((reveal pl <: Seq.seq U8.t) == reveal d /\
              reveal o' == tftp_serialize (Msg_data blk (reveal pl)))
{
  let pl = ID.indefinite_description_ghost data_payload
    (fun (pl:data_payload) ->
      (pl <: Seq.seq U8.t) == reveal d /\
      reveal o' == tftp_serialize (Msg_data blk pl));
  hide pl
}

(* ── network processing: dispatch on the single serialized datagram ───────── *)

fn tftp_server_process_network
  (i:tftp_server_impl)
  (frame:tftp_server_network_frame)
  (input:array U8.t)
  (input_len:SZ.t)
  (out:array U8.t)
  (out_len:SZ.t)
  (received0:erased TCP.bytes)
  (sent0:erased TCP.bytes)
  (st0:erased TP.tftp_server_state)
  (input_contents:erased TCP.bytes)
  (old_out:erased TCP.bytes)
requires
  tftp_server_inv i received0 sent0 st0 **
  tftp_server_network_frame_pre frame input input_len out out_len input_contents old_out **
  pts_to input input_contents **
  pts_to out old_out **
  pure (CPI.buffers_wf (Ghost.reveal input_contents) input_len (Ghost.reveal old_out) out_len)
returns result:CPI.process_result
ensures exists* (received1:Ghost.erased TCP.bytes)
                (sent1:Ghost.erased TCP.bytes)
                (st1:Ghost.erased TP.tftp_server_state)
                (out_contents:TCP.bytes)
                (consumed:TCP.bytes)
                (wire_outputs:list tftp_message)
                (local_outputs:list unit).
  tftp_server_inv i (Ghost.reveal received1) (Ghost.reveal sent1) (Ghost.reveal st1) **
  tftp_server_network_frame_post
    frame result input_contents input_len old_out out_contents st0 (Ghost.reveal st1)
    consumed wire_outputs local_outputs **
  pts_to input input_contents **
  pts_to out out_contents **
  pure (
    CPI.network_process_correct
      (TP.tftp_server_wfsm)
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
  unfold (tftp_server_inv i received0 sent0 st0);
  with svs evs. _;
  let s = Vec.op_Dot_Lparen_Rparen i.status 0sz;
  unfold (tftp_server_network_frame_pre frame input input_len out out_len input_contents old_out);
  with d0. _;
  if (input_len = 4sz) {
    let b0 = input.(0sz);
    let b1 = input.(1sz);
    let ha = Codec.u16_hi op_ack;
    let la = Codec.u16_lo op_ack;
    if (s = 1uy && b0 = ha && b1 = la) {
      (* ACK in the one-outstanding state: recover the block number. *)
      let blk = Codec.tftp_recv_ack input;
      let exp = Vec.op_Dot_Lparen_Rparen i.expected 0sz;
      if (blk = exp) {
        (* StepOk — the acked block equals the outstanding one; advance acked. *)
        Log.lemma_ack_parse_eval (Ghost.reveal input_contents);
        Log.lemma_input_is_serialize_ack (Ghost.reveal input_contents) blk;
        Log.lemma_ack_step (Ghost.reveal st0) blk;
        let st1 = Ghost.hide (Log.ack_next_state (Ghost.reveal st0));
        let received1 = Ghost.hide (Seq.append (Ghost.reveal received0) (Ghost.reveal input_contents));
        Vec.op_Dot_Lparen_Rparen_Less_Minus i.status 0sz 0uy;
        with svs2. _;
        let log0 = Ghost.hide (Log.mk_log (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st0));
        let log1 = Ghost.hide (Log.mk_log (Ghost.reveal received1) (Ghost.reveal sent0) (Ghost.reveal st1));
        Log.lemma_ack_advance (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st0) blk;
        RTC.closure_step Log.ts_step_rel (Ghost.reveal log0) (Ghost.reveal log1);
        MR.update i.progress (Ghost.reveal log1);
        fold (tftp_server_inv i (Ghost.reveal received1) (Ghost.reveal sent0) (Ghost.reveal st1));
        Log.lemma_output_written_empty (Ghost.reveal old_out);
        Seq.append_empty_r (Ghost.reveal sent0);
        Log.lemma_network_stepok
          (Ghost.reveal input_contents) input_len (Ghost.reveal old_out) (Ghost.reveal old_out) out_len
          (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st0)
          (Msg_ack blk) (Ghost.reveal st1) 0sz [] Seq.empty;
        fold (tftp_server_network_frame_post
          frame (Log.ts_result CPI.StepOk input_len 0sz) input_contents input_len old_out old_out
          (Ghost.reveal st0) (Ghost.reveal st1) (Ghost.reveal input_contents) [] []);
        Log.ts_result CPI.StepOk input_len 0sz
      } else {
        (* ACK for a stale block: a sound IllegalTransition no-op. *)
        Log.lemma_network_noop
          (Ghost.reveal input_contents) input_len (Ghost.reveal old_out) out_len
          (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st0);
        fold (tftp_server_inv i (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st0));
        fold (tftp_server_network_frame_post
          frame (Log.ts_result CPI.IllegalTransition 0sz 0sz) input_contents input_len old_out (Ghost.reveal old_out)
          (Ghost.reveal st0) (Ghost.reveal st0) Seq.empty [] []);
        Log.ts_result CPI.IllegalTransition 0sz 0sz
      }
    } else {
      (* Not an ACK we expect: a sound IllegalTransition no-op. *)
      Log.lemma_network_noop
        (Ghost.reveal input_contents) input_len (Ghost.reveal old_out) out_len
        (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st0);
      fold (tftp_server_inv i (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st0));
      fold (tftp_server_network_frame_post
        frame (Log.ts_result CPI.IllegalTransition 0sz 0sz) input_contents input_len old_out (Ghost.reveal old_out)
        (Ghost.reveal st0) (Ghost.reveal st0) Seq.empty [] []);
      Log.ts_result CPI.IllegalTransition 0sz 0sz
    }
  } else if (input_len = 5sz) {
    let b0 = input.(0sz);
    let b1 = input.(1sz);
    let b4 = input.(4sz);
    let he = Codec.u16_hi op_error;
    let le = Codec.u16_lo op_error;
    if ((s = 0uy || s = 1uy) && b0 = he && b1 = le && b4 = 0uy) {
      (* ERROR (minimal 5-byte form) while InProgress: StepOk — flip to Aborted. *)
      let b2 = input.(2sz);
      let b3 = input.(3sz);
      let code = Codec.u16_of_bytes b2 b3;
      Log.lemma_input_is_serialize_error (Ghost.reveal input_contents) code;
      Log.lemma_error_step (Ghost.reveal st0) code (Seq.empty <: cstring);
      let st1 = Ghost.hide (Log.abort_next_state (Ghost.reveal st0));
      let received1 = Ghost.hide (Seq.append (Ghost.reveal received0) (Ghost.reveal input_contents));
      Vec.op_Dot_Lparen_Rparen_Less_Minus i.status 0sz 3uy;
      with svs2. _;
      let log0 = Ghost.hide (Log.mk_log (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st0));
      let log1 = Ghost.hide (Log.mk_log (Ghost.reveal received1) (Ghost.reveal sent0) (Ghost.reveal st1));
      Log.lemma_error_advance (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st0) code;
      RTC.closure_step Log.ts_step_rel (Ghost.reveal log0) (Ghost.reveal log1);
      MR.update i.progress (Ghost.reveal log1);
      fold (tftp_server_inv i (Ghost.reveal received1) (Ghost.reveal sent0) (Ghost.reveal st1));
      Log.lemma_output_written_empty (Ghost.reveal old_out);
      Seq.append_empty_r (Ghost.reveal sent0);
      Log.lemma_network_stepok
        (Ghost.reveal input_contents) input_len (Ghost.reveal old_out) (Ghost.reveal old_out) out_len
        (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st0)
        (Msg_error code (Seq.empty <: cstring)) (Ghost.reveal st1) 0sz [] Seq.empty;
      fold (tftp_server_network_frame_post
        frame (Log.ts_result CPI.StepOk input_len 0sz) input_contents input_len old_out old_out
        (Ghost.reveal st0) (Ghost.reveal st1) (Ghost.reveal input_contents) [] []);
      Log.ts_result CPI.StepOk input_len 0sz
    } else {
      (* Not the minimal ERROR (or already terminated): a sound no-op. *)
      Log.lemma_network_noop
        (Ghost.reveal input_contents) input_len (Ghost.reveal old_out) out_len
        (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st0);
      fold (tftp_server_inv i (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st0));
      fold (tftp_server_network_frame_post
        frame (Log.ts_result CPI.IllegalTransition 0sz 0sz) input_contents input_len old_out (Ghost.reveal old_out)
        (Ghost.reveal st0) (Ghost.reveal st0) Seq.empty [] []);
      Log.ts_result CPI.IllegalTransition 0sz 0sz
    }
  } else {
    (* Any other datagram length: a sound IllegalTransition no-op. *)
    Log.lemma_network_noop
      (Ghost.reveal input_contents) input_len (Ghost.reveal old_out) out_len
      (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st0);
    fold (tftp_server_inv i (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st0));
    fold (tftp_server_network_frame_post
      frame (Log.ts_result CPI.IllegalTransition 0sz 0sz) input_contents input_len old_out (Ghost.reveal old_out)
      (Ghost.reveal st0) (Ghost.reveal st0) Seq.empty [] []);
    Log.ts_result CPI.IllegalTransition 0sz 0sz
  }
}

(* ── local processing: drive the five local events ────────────────────────── *)

fn tftp_server_process_local
  (i:tftp_server_impl)
  (ev:TP.tftp_server_local)
  (frame:tftp_server_local_frame)
  (out:array U8.t)
  (out_len:SZ.t)
  (received0:erased TCP.bytes)
  (sent0:erased TCP.bytes)
  (st0:erased TP.tftp_server_state)
  (old_out:erased TCP.bytes)
requires
  tftp_server_inv i received0 sent0 st0 **
  tftp_server_local_frame_pre ev frame st0 out out_len old_out **
  pts_to out old_out **
  pure (
    SZ.v out_len == Seq.length old_out /\
    ~ (CPI.no_internal_events #TP.tftp_server_local ev))
returns result:CPI.process_result
ensures exists* (received1:Ghost.erased TCP.bytes)
                (sent1:Ghost.erased TCP.bytes)
                (st1:Ghost.erased TP.tftp_server_state)
                (out_contents:TCP.bytes)
                (wire_outputs:list tftp_message)
                (local_outputs:list unit).
  tftp_server_inv i (Ghost.reveal received1) (Ghost.reveal sent1) (Ghost.reveal st1) **
  tftp_server_local_frame_post
    ev frame result old_out out_contents st0 (Ghost.reveal st1)
    wire_outputs local_outputs **
  pts_to out out_contents **
  pure (
    CPI.local_process_correct
      (TP.tftp_server_wfsm)
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
  unfold (tftp_server_inv i received0 sent0 st0);
  with svs evs. _;
  let s = Vec.op_Dot_Lparen_Rparen i.status 0sz;
  unfold (tftp_server_local_frame_pre ev frame st0 out out_len old_out);
  with d. _;
  match ev {
    TP.Server_start filename plan -> {
      (* StepOk — initialise the transfer; the "idle" cell 0uy is unchanged. *)
      Log.lemma_start_step (Ghost.reveal st0) filename plan;
      let st1 = Ghost.hide (Log.start_next_state filename plan);
      Vec.op_Dot_Lparen_Rparen_Less_Minus i.status 0sz 0uy;
      with svs2. _;
      let log0 = Ghost.hide (Log.mk_log (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st0));
      let log1 = Ghost.hide (Log.mk_log (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st1));
      Log.lemma_start_advance (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st0) filename plan;
      RTC.closure_step Log.ts_step_rel (Ghost.reveal log0) (Ghost.reveal log1);
      MR.update i.progress (Ghost.reveal log1);
      fold (tftp_server_inv i (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st1));
      Log.lemma_output_written_empty (Ghost.reveal old_out);
      Seq.append_empty_r (Ghost.reveal sent0);
      Log.lemma_local_stepok ev (Ghost.reveal old_out) (Ghost.reveal old_out) out_len
        (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st0)
        0sz (Ghost.reveal st1) [] Seq.empty;
      fold (tftp_server_local_frame_post ev frame (Log.ts_result CPI.StepOk 0sz 0sz)
        old_out (Ghost.reveal old_out) (Ghost.reveal st0) (Ghost.reveal st1) [] []);
      Log.ts_result CPI.StepOk 0sz 0sz
    }
    TP.Server_send -> {
      (* StepOk — frame + emit the next DATA block; enter one-outstanding. *)
      Codec.tftp_emit_data frame.tslf_blk frame.tslf_buf frame.tslf_len out;
      with o'. _;
      let pl = extract_data_payload d o' frame.tslf_blk;
      Seq.lemma_eq_elim (L.hd (Ghost.reveal st0).TP.tss_pending) (Ghost.reveal d);
      Log.lemma_send_step (Ghost.reveal st0) frame.tslf_blk (Ghost.reveal pl);
      let st1 = Ghost.hide (Log.send_next_state (Ghost.reveal st0));
      let sent1 = Ghost.hide (Seq.append (Ghost.reveal sent0) (tftp_serialize (Msg_data frame.tslf_blk (Ghost.reveal pl))));
      Vec.op_Dot_Lparen_Rparen_Less_Minus i.status 0sz 1uy;
      with svs2. _;
      Vec.op_Dot_Lparen_Rparen_Less_Minus i.expected 0sz frame.tslf_blk;
      with evs2. _;
      let log0 = Ghost.hide (Log.mk_log (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st0));
      let log1 = Ghost.hide (Log.mk_log (Ghost.reveal received0) (Ghost.reveal sent1) (Ghost.reveal st1));
      Log.lemma_send_advance (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st0) frame.tslf_blk (Ghost.reveal pl);
      RTC.closure_step Log.ts_step_rel (Ghost.reveal log0) (Ghost.reveal log1);
      MR.update i.progress (Ghost.reveal log1);
      fold (tftp_server_inv i (Ghost.reveal received0) (Ghost.reveal sent1) (Ghost.reveal st1));
      Log.lemma_tftp_serialize_all_singleton (Msg_data frame.tslf_blk (Ghost.reveal pl));
      Log.lemma_data_output_written (Ghost.reveal o') out_len frame.tslf_blk (Ghost.reveal pl);
      Log.lemma_local_stepok ev (Ghost.reveal old_out) (Ghost.reveal o') out_len
        (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st0)
        out_len (Ghost.reveal st1) [Msg_data frame.tslf_blk (Ghost.reveal pl)]
        (tftp_serialize (Msg_data frame.tslf_blk (Ghost.reveal pl)));
      fold (tftp_server_local_frame_post ev frame (Log.ts_result CPI.StepOk 0sz out_len)
        old_out (Ghost.reveal o') (Ghost.reveal st0) (Ghost.reveal st1)
        [Msg_data frame.tslf_blk (Ghost.reveal pl)] []);
      Log.ts_result CPI.StepOk 0sz out_len
    }
    TP.Server_complete -> {
      (* StepOk — the final block was acked; flip the status to Completed (2uy). *)
      Log.lemma_complete_step (Ghost.reveal st0);
      let st1 = Ghost.hide (Log.complete_next_state (Ghost.reveal st0));
      Vec.op_Dot_Lparen_Rparen_Less_Minus i.status 0sz 2uy;
      with svs2. _;
      let log0 = Ghost.hide (Log.mk_log (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st0));
      let log1 = Ghost.hide (Log.mk_log (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st1));
      Log.lemma_complete_advance (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st0);
      RTC.closure_step Log.ts_step_rel (Ghost.reveal log0) (Ghost.reveal log1);
      MR.update i.progress (Ghost.reveal log1);
      fold (tftp_server_inv i (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st1));
      Log.lemma_output_written_empty (Ghost.reveal old_out);
      Seq.append_empty_r (Ghost.reveal sent0);
      Log.lemma_local_stepok ev (Ghost.reveal old_out) (Ghost.reveal old_out) out_len
        (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st0)
        0sz (Ghost.reveal st1) [] Seq.empty;
      fold (tftp_server_local_frame_post ev frame (Log.ts_result CPI.StepOk 0sz 0sz)
        old_out (Ghost.reveal old_out) (Ghost.reveal st0) (Ghost.reveal st1) [] []);
      Log.ts_result CPI.StepOk 0sz 0sz
    }
    TP.Server_timeout -> {
      if (s = 1uy) {
        (* One outstanding: retransmit sent[acked]; abstract state unchanged. *)
        assert (pure ((Ghost.reveal st0).TP.tss_acked < L.length (Ghost.reveal st0).TP.tss_sent));
        Codec.tftp_emit_data frame.tslf_blk frame.tslf_buf frame.tslf_len out;
        with o'. _;
        let pl = extract_data_payload d o' frame.tslf_blk;
        Seq.lemma_eq_elim (L.index (Ghost.reveal st0).TP.tss_sent (Ghost.reveal st0).TP.tss_acked) (Ghost.reveal d);
        Log.lemma_timeout_step (Ghost.reveal st0) frame.tslf_blk (Ghost.reveal pl);
        let sent1 = Ghost.hide (Seq.append (Ghost.reveal sent0) (tftp_serialize (Msg_data frame.tslf_blk (Ghost.reveal pl))));
        let log0 = Ghost.hide (Log.mk_log (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st0));
        let log1 = Ghost.hide (Log.mk_log (Ghost.reveal received0) (Ghost.reveal sent1) (Ghost.reveal st0));
        Log.lemma_timeout_advance (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st0) frame.tslf_blk (Ghost.reveal pl);
        RTC.closure_step Log.ts_step_rel (Ghost.reveal log0) (Ghost.reveal log1);
        MR.update i.progress (Ghost.reveal log1);
        fold (tftp_server_inv i (Ghost.reveal received0) (Ghost.reveal sent1) (Ghost.reveal st0));
        Log.lemma_tftp_serialize_all_singleton (Msg_data frame.tslf_blk (Ghost.reveal pl));
        Log.lemma_data_output_written (Ghost.reveal o') out_len frame.tslf_blk (Ghost.reveal pl);
        Log.lemma_local_stepok ev (Ghost.reveal old_out) (Ghost.reveal o') out_len
          (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st0)
          out_len (Ghost.reveal st0) [Msg_data frame.tslf_blk (Ghost.reveal pl)]
          (tftp_serialize (Msg_data frame.tslf_blk (Ghost.reveal pl)));
        fold (tftp_server_local_frame_post ev frame (Log.ts_result CPI.StepOk 0sz out_len)
          old_out (Ghost.reveal o') (Ghost.reveal st0) (Ghost.reveal st0)
          [Msg_data frame.tslf_blk (Ghost.reveal pl)] []);
        Log.ts_result CPI.StepOk 0sz out_len
      } else {
        (* No block in flight (or terminated): a sound IllegalTransition no-op. *)
        Log.lemma_local_illegal ev (Ghost.reveal old_out) (Ghost.reveal old_out) out_len
          (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st0);
        fold (tftp_server_inv i (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st0));
        fold (tftp_server_local_frame_post ev frame (Log.ts_result CPI.IllegalTransition 0sz 0sz)
          old_out (Ghost.reveal old_out) (Ghost.reveal st0) (Ghost.reveal st0) [] []);
        Log.ts_result CPI.IllegalTransition 0sz 0sz
      }
    }
    TP.Server_abort -> {
      (* StepOk — cancel; flip the status to Aborted (cell 3uy). *)
      Log.lemma_abort_step (Ghost.reveal st0);
      let st1 = Ghost.hide (Log.abort_next_state (Ghost.reveal st0));
      Vec.op_Dot_Lparen_Rparen_Less_Minus i.status 0sz 3uy;
      with svs2. _;
      let log0 = Ghost.hide (Log.mk_log (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st0));
      let log1 = Ghost.hide (Log.mk_log (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st1));
      Log.lemma_abort_advance (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st0);
      RTC.closure_step Log.ts_step_rel (Ghost.reveal log0) (Ghost.reveal log1);
      MR.update i.progress (Ghost.reveal log1);
      fold (tftp_server_inv i (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st1));
      Log.lemma_output_written_empty (Ghost.reveal old_out);
      Seq.append_empty_r (Ghost.reveal sent0);
      Log.lemma_local_stepok ev (Ghost.reveal old_out) (Ghost.reveal old_out) out_len
        (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st0)
        0sz (Ghost.reveal st1) [] Seq.empty;
      fold (tftp_server_local_frame_post ev frame (Log.ts_result CPI.StepOk 0sz 0sz)
        old_out (Ghost.reveal old_out) (Ghost.reveal st0) (Ghost.reveal st1) [] []);
      Log.ts_result CPI.StepOk 0sz 0sz
    }
  }
}

(* ── constructor: a freshly-created, un-started sender ────────────────────── *)

fn new_tftp_server ()
requires emp
returns i:tftp_server_impl
ensures tftp_server_inv i Seq.empty Seq.empty TP.tftp_server_initial **
        pure (Vec.is_full_vec i.status /\ Vec.is_full_vec i.expected)
{
  let status = Vec.alloc 0uy 1sz;
  let expected = Vec.alloc 0us 1sz;
  let progress =
    MR.alloc #_ #Log.ts_state_ahead_preorder
      (Log.mk_log Seq.empty Seq.empty TP.tftp_server_initial);
  let i = { status; expected; progress };
  rewrite (MR.pts_to progress #1.0R (Log.mk_log Seq.empty Seq.empty TP.tftp_server_initial)) as
          (MR.pts_to i.progress #1.0R (Log.mk_log Seq.empty Seq.empty TP.tftp_server_initial));
  with sv. rewrite (Vec.pts_to status sv) as (Vec.pts_to i.status sv);
  with ev. rewrite (Vec.pts_to expected ev) as (Vec.pts_to i.expected ev);
  Log.lemma_initial_trace_ok ();
  fold (tftp_server_inv i Seq.empty Seq.empty TP.tftp_server_initial);
  assert (pure (Vec.is_full_vec i.status /\ Vec.is_full_vec i.expected));
  i
}

(* ── the instance ─────────────────────────────────────────────────────────── *)

noextract
let tftp_server_protocol_implementation
  : CPI.protocol_implementation
      tftp_server_impl
      TP.tftp_server_state
      tftp_message
      TP.tftp_server_local
      unit
  =
  {
    CPI.pi_system = (fun _ -> TP.tftp_server_wfsm);
    CPI.pi_internal = CPI.no_internal_events #TP.tftp_server_local;
    CPI.pi_internal_pending = CPI.nothing_pending #TP.tftp_server_state;
    CPI.pi_invariant = tftp_server_inv;
    CPI.pi_snapshot = tftp_server_snap;
    CPI.pi_network_frame = tftp_server_network_frame;
    CPI.pi_network_frame_pre = tftp_server_network_frame_pre;
    CPI.pi_network_frame_post = tftp_server_network_frame_post;
    CPI.pi_local_frame = tftp_server_local_frame;
    CPI.pi_local_frame_pre = tftp_server_local_frame_pre;
    CPI.pi_local_frame_post = tftp_server_local_frame_post;
    CPI.pi_internal_frame_pre =
      CPI.no_internal_frame_pre #tftp_server_local_frame #TP.tftp_server_state;
    CPI.pi_internal_frame_post =
      CPI.no_internal_frame_post #tftp_server_local_frame #TP.tftp_server_state #tftp_message #unit;
    CPI.pi_invariant_valid = tftp_server_invariant_valid;
    CPI.pi_take_snapshot = tftp_server_take_snapshot;
    CPI.pi_recall_snapshot = tftp_server_recall_snapshot;
    CPI.pi_process_network = tftp_server_process_network;
    CPI.pi_process_local = tftp_server_process_local;
    CPI.pi_process_internal =
      CPI.quiescent_process_internal
        #_ #TP.tftp_server_state #tftp_message #TP.tftp_server_local #unit #tftp_server_local_frame
        tftp_server_inv
        (fun _ -> TP.tftp_server_wfsm);
  }
