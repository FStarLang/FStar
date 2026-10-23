module Calc.Server.Endpoint

#lang-pulse

open Pulse.Lib.Pervasives

module CPI = Pulse.Lib.Protocol.Implementation
module PD = Pulse.Lib.Protocol.Driver
module PE = Pulse.Lib.Protocol.Endpoint
module R = Pulse.Lib.Reference
module Seq = FStar.Seq
module SZ = FStar.SizeT
module TCP = Pulse.Lib.TCP
module U8 = FStar.UInt8
module Vec = Pulse.Lib.Vec
module MR = Pulse.Lib.MonotonicGhostRef

module CalcCP = Calc.Server.CanonicalProtocol
module CalcP = Calc.Protocol

open Calc.Log
open Calc.Wire
open Calc.Impl.Types

type calc_endpoint_config = unit

let calc_empty_bytes : TCP.bytes = Seq.empty

type calc_driver_status =
  | CalcDriverNetworkStep
  | CalcDriverFailed

noeq
type calc_driver_result = {
  calc_driver_status: calc_driver_status;
}

inline_for_extraction
let calc_network_driver_status
  (result:CPI.process_result)
  : Tot (status:calc_driver_status) =
  match result.CPI.process_status with
  | CPI.StepOk
  | CPI.NeedMoreInput -> CalcDriverNetworkStep
  | CPI.ParseFailed
  | CPI.DecodeError
  | CPI.IllegalTransition
  | CPI.OutputBufferTooSmall
  | CPI.ConnectionFailed -> CalcDriverFailed

[@@pulse_unfold]
let calc_frame_ready
  (_srv:CalcCP.canonical_server)
  (_cfg:calc_endpoint_config)
  (frame:CalcCP.calc_network_frame)
  (_log:calc_log)
  : slprop =
  pure (
    Vec.length frame.CalcCP.calc_network_req == 5 /\
    Vec.length frame.CalcCP.calc_network_resp == 5 /\
    Vec.is_full_vec frame.CalcCP.calc_network_req /\
    Vec.is_full_vec frame.CalcCP.calc_network_resp)

[@@pulse_unfold]
let calc_io_ready
  (_srv:CalcCP.canonical_server)
  (ch:TCP.channel)
  (frame:CalcCP.calc_network_frame)
  (_received:TCP.bytes)
  (sent:TCP.bytes)
  (_log:calc_log)
  : slprop =
  exists* raw_received req_bytes resp_bytes.
    TCP.is_channel ch raw_received sent **
    Vec.pts_to frame.CalcCP.calc_network_req req_bytes **
    Vec.pts_to frame.CalcCP.calc_network_resp resp_bytes **
    pure (
      Seq.length req_bytes == 5 /\
      Seq.length resp_bytes == 5 /\
      Vec.length frame.CalcCP.calc_network_req == 5 /\
      Vec.length frame.CalcCP.calc_network_resp == 5 /\
      Vec.is_full_vec frame.CalcCP.calc_network_req /\
      Vec.is_full_vec frame.CalcCP.calc_network_resp)

let calc_action_frame
  (srv:CalcCP.canonical_server)
  (cfg:calc_endpoint_config)
  (frame:CalcCP.calc_network_frame)
  (log:calc_log)
  (action:PE.endpoint_action
    CalcCP.calc_network_frame
    CalcP.calc_frame_local_event
    CalcCP.calc_local_frame)
  : slprop =
  match action with
  | PE.EndpointNeedInput network_frame ->
    calc_frame_ready srv cfg frame log **
    pure (network_frame == frame)
  | PE.EndpointLocal _ _ ->
    pure False
  | PE.EndpointDone
  | PE.EndpointFailed ->
    calc_frame_ready srv cfg frame log

let calc_network_continuation
  (srv:CalcCP.canonical_server)
  (cfg:calc_endpoint_config)
  (frame:CalcCP.calc_network_frame)
  (_log:calc_log)
  (_network_frame:CalcCP.calc_network_frame)
  : slprop =
  calc_frame_ready srv cfg frame _log

let calc_local_continuation
  (srv:CalcCP.canonical_server)
  (cfg:calc_endpoint_config)
  (frame:CalcCP.calc_network_frame)
  (_log:calc_log)
  (_ev:CalcP.calc_frame_local_event)
  (_local_frame:CalcCP.calc_local_frame)
  : slprop =
  calc_frame_ready srv cfg frame _log

noeq
type calc_network_io = {
  calc_nio_input: array U8.t;
  calc_nio_input_len: SZ.t;
  calc_nio_output: array U8.t;
  calc_nio_input_contents: Ghost.erased TCP.bytes;
  calc_nio_old_output: Ghost.erased TCP.bytes;
  calc_nio_raw_received: Ghost.erased TCP.bytes;
}

let calc_network_io_continuation
  (_srv:CalcCP.canonical_server)
  (ch:TCP.channel)
  (_frame:CalcCP.calc_network_frame)
  (_received:TCP.bytes)
  (sent:TCP.bytes)
  (_log:calc_log)
  (nio:calc_network_io)
  : slprop =
  TCP.is_channel ch (Ghost.reveal nio.calc_nio_raw_received) sent **
  pure (
    nio.calc_nio_input == Vec.vec_to_array _frame.CalcCP.calc_network_req /\
    nio.calc_nio_output == Vec.vec_to_array _frame.CalcCP.calc_network_resp /\
    nio.calc_nio_input_len == 5sz /\
    Seq.length (Ghost.reveal nio.calc_nio_input_contents) == 5 /\
    Seq.length (Ghost.reveal nio.calc_nio_old_output) == 5 /\
    Vec.length _frame.CalcCP.calc_network_req == 5 /\
    Vec.length _frame.CalcCP.calc_network_resp == 5 /\
    Vec.is_full_vec _frame.CalcCP.calc_network_req /\
    Vec.is_full_vec _frame.CalcCP.calc_network_resp)

inline_for_extraction
let calc_network_input (nio:calc_network_io) : array U8.t =
  nio.calc_nio_input

inline_for_extraction
let calc_network_input_len (nio:calc_network_io) : SZ.t =
  nio.calc_nio_input_len

inline_for_extraction
let calc_network_output (nio:calc_network_io) : array U8.t =
  nio.calc_nio_output

inline_for_extraction
let calc_network_output_len (_nio:calc_network_io) : SZ.t =
  5sz

let calc_network_input_contents (nio:calc_network_io) : Ghost.erased TCP.bytes =
  nio.calc_nio_input_contents

let calc_network_old_output (nio:calc_network_io) : Ghost.erased TCP.bytes =
  nio.calc_nio_old_output

noextract
fn calc_next_action
  (srv:CalcCP.canonical_server)
  (cfg:calc_endpoint_config)
  (frame:CalcCP.calc_network_frame)
  (received:Ghost.erased TCP.bytes)
  (sent:Ghost.erased TCP.bytes)
  (log:Ghost.erased calc_log)
requires
  CalcCP.canonical_server_exactly srv (Ghost.reveal received) (Ghost.reveal sent) (Ghost.reveal log) **
  calc_frame_ready srv cfg frame (Ghost.reveal log)
returns action:PE.endpoint_action
  CalcCP.calc_network_frame
  CalcP.calc_frame_local_event
  CalcCP.calc_local_frame
ensures
  CalcCP.canonical_server_exactly srv (Ghost.reveal received) (Ghost.reveal sent) (Ghost.reveal log) **
  calc_action_frame srv cfg frame (Ghost.reveal log) action **
  pure (PE.action_not_internal CalcCP.calc_server_protocol_implementation action)
{
  unfold (calc_frame_ready srv cfg frame (Ghost.reveal log));
  fold (calc_action_frame srv cfg frame (Ghost.reveal log) (PE.EndpointNeedInput frame));
  PE.EndpointNeedInput frame
}

noextract
fn calc_cancel_action
  (srv:CalcCP.canonical_server)
  (cfg:calc_endpoint_config)
  (frame:CalcCP.calc_network_frame)
  (log:Ghost.erased calc_log)
  (action:PE.endpoint_action
    CalcCP.calc_network_frame
    CalcP.calc_frame_local_event
    CalcCP.calc_local_frame)
requires calc_action_frame srv cfg frame (Ghost.reveal log) action
ensures calc_frame_ready srv cfg frame (Ghost.reveal log)
{
  match action {
    PE.EndpointNeedInput network_frame -> {
      unfold (calc_action_frame srv cfg frame (Ghost.reveal log) (PE.EndpointNeedInput network_frame));
      fold (calc_frame_ready srv cfg frame (Ghost.reveal log))
    }
    PE.EndpointLocal ev local_frame -> {
      unfold (calc_action_frame srv cfg frame (Ghost.reveal log) (PE.EndpointLocal ev local_frame));
      assert (pure False);
      fold (calc_frame_ready srv cfg frame (Ghost.reveal log))
    }
    PE.EndpointDone -> {
      unfold (calc_action_frame srv cfg frame (Ghost.reveal log) PE.EndpointDone)
    }
    PE.EndpointFailed -> {
      unfold (calc_action_frame srv cfg frame (Ghost.reveal log) PE.EndpointFailed)
    }
  }
}

inline_for_extraction
fn calc_prepare_network_io
  (srv:CalcCP.canonical_server)
  (ch:TCP.channel)
  (frame:CalcCP.calc_network_frame)
  (received:Ghost.erased TCP.bytes)
  (sent:Ghost.erased TCP.bytes)
  (log:Ghost.erased calc_log)
requires calc_io_ready srv ch frame (Ghost.reveal received) (Ghost.reveal sent) (Ghost.reveal log)
returns nio:calc_network_io
ensures
  calc_network_io_continuation srv ch frame (Ghost.reveal received) (Ghost.reveal sent) (Ghost.reveal log) nio **
  PE.network_buffers
    (calc_network_input nio)
    (calc_network_input_len nio)
    (calc_network_output nio)
    (calc_network_output_len nio)
    (Ghost.reveal (calc_network_input_contents nio))
    (Ghost.reveal (calc_network_old_output nio))
{
  unfold (calc_io_ready srv ch frame (Ghost.reveal received) (Ghost.reveal sent) (Ghost.reveal log));
  with raw_received req_bytes resp_bytes. _;
  Vec.to_array_pts_to frame.CalcCP.calc_network_req;
  let nread = TCP.read_full ch (Vec.vec_to_array frame.CalcCP.calc_network_req) 5sz;
  with req_bytes_after chunk. _;
  assert (pure (nread == 5sz));
  assert (pure (Seq.length req_bytes_after == 5));
  assert (pure (Seq.length chunk == 5));
  Vec.to_array_pts_to frame.CalcCP.calc_network_resp;
  let inpute = Ghost.hide req_bytes_after;
  let old_oute = Ghost.hide resp_bytes;
  let raw_aftere = Ghost.hide (Seq.append raw_received chunk);
  let nio = {
    calc_nio_input = Vec.vec_to_array frame.CalcCP.calc_network_req;
    calc_nio_input_len = nread;
    calc_nio_output = Vec.vec_to_array frame.CalcCP.calc_network_resp;
    calc_nio_input_contents = inpute;
    calc_nio_old_output = old_oute;
    calc_nio_raw_received = raw_aftere;
  };
  assert (pure (Ghost.reveal inpute == req_bytes_after));
  assert (pure (Ghost.reveal old_oute == resp_bytes));
  assert (pure (Ghost.reveal raw_aftere == Seq.append raw_received chunk));
  assert (pure (nio.calc_nio_raw_received == raw_aftere));
  rewrite
    (TCP.is_channel ch (Seq.append raw_received chunk) (Ghost.reveal sent))
    as
    (TCP.is_channel ch (Ghost.reveal raw_aftere) (Ghost.reveal sent));
  rewrite
    (TCP.is_channel ch (Ghost.reveal raw_aftere) (Ghost.reveal sent))
    as
    (TCP.is_channel ch (Ghost.reveal nio.calc_nio_raw_received) (Ghost.reveal sent));
  fold (calc_network_io_continuation
    srv
    ch
    frame
    (Ghost.reveal received)
    (Ghost.reveal sent)
    (Ghost.reveal log)
    nio);
  assert (pure (calc_network_input nio == Vec.vec_to_array frame.CalcCP.calc_network_req));
  assert (pure (calc_network_output nio == Vec.vec_to_array frame.CalcCP.calc_network_resp));
  assert (pure (calc_network_input_len nio == 5sz));
  assert (pure (calc_network_input_contents nio == inpute));
  assert (pure (calc_network_old_output nio == old_oute));
  rewrite
    (pts_to (Vec.vec_to_array frame.CalcCP.calc_network_req) req_bytes_after)
    as
    (pts_to (calc_network_input nio) (Ghost.reveal (calc_network_input_contents nio)));
  rewrite
    (pts_to (Vec.vec_to_array frame.CalcCP.calc_network_resp) resp_bytes)
    as
    (pts_to (calc_network_output nio) (Ghost.reveal (calc_network_old_output nio)));
  fold (PE.network_buffers
    (calc_network_input nio)
    (calc_network_input_len nio)
    (calc_network_output nio)
    (calc_network_output_len nio)
    (Ghost.reveal (calc_network_input_contents nio))
    (Ghost.reveal (calc_network_old_output nio)));
  nio
}

inline_for_extraction
fn calc_prepare_network_action
  (srv:CalcCP.canonical_server)
  (cfg:calc_endpoint_config)
  (frame:CalcCP.calc_network_frame)
  (ch:TCP.channel)
  (nio:calc_network_io)
  (network_frame:CalcCP.calc_network_frame)
  (received:Ghost.erased TCP.bytes)
  (sent:Ghost.erased TCP.bytes)
  (log:Ghost.erased calc_log)
requires
  calc_action_frame srv cfg frame (Ghost.reveal log) (PE.EndpointNeedInput network_frame) **
  calc_network_io_continuation srv ch frame (Ghost.reveal received) (Ghost.reveal sent) (Ghost.reveal log) nio **
  PE.network_buffers
    (calc_network_input nio)
    (calc_network_input_len nio)
    (calc_network_output nio)
    (calc_network_output_len nio)
    (Ghost.reveal (calc_network_input_contents nio))
    (Ghost.reveal (calc_network_old_output nio))
ensures
  CalcCP.calc_network_frame_pre
    network_frame
    (calc_network_input nio)
    (calc_network_input_len nio)
    (calc_network_output nio)
    (calc_network_output_len nio)
    (Ghost.reveal (calc_network_input_contents nio))
    (Ghost.reveal (calc_network_old_output nio)) **
  calc_network_continuation srv cfg frame (Ghost.reveal log) network_frame **
  calc_network_io_continuation srv ch frame (Ghost.reveal received) (Ghost.reveal sent) (Ghost.reveal log) nio **
  PE.network_buffers
    (calc_network_input nio)
    (calc_network_input_len nio)
    (calc_network_output nio)
    (calc_network_output_len nio)
    (Ghost.reveal (calc_network_input_contents nio))
    (Ghost.reveal (calc_network_old_output nio)) **
  pure (
    CPI.buffers_wf
      (Ghost.reveal (calc_network_input_contents nio))
      (calc_network_input_len nio)
      (Ghost.reveal (calc_network_old_output nio))
      (calc_network_output_len nio))
{
  unfold (calc_action_frame srv cfg frame (Ghost.reveal log) (PE.EndpointNeedInput network_frame));
  unfold (calc_network_io_continuation srv ch frame (Ghost.reveal received) (Ghost.reveal sent) (Ghost.reveal log) nio);
  unfold (PE.network_buffers
    (calc_network_input nio)
    (calc_network_input_len nio)
    (calc_network_output nio)
    (calc_network_output_len nio)
    (Ghost.reveal (calc_network_input_contents nio))
    (Ghost.reveal (calc_network_old_output nio)));
  rewrite (CalcCP.calc_network_frame_pre
    frame
    (calc_network_input nio)
    (calc_network_input_len nio)
    (calc_network_output nio)
    (calc_network_output_len nio)
    (Ghost.reveal (calc_network_input_contents nio))
    (Ghost.reveal (calc_network_old_output nio)))
    as
    (CalcCP.calc_network_frame_pre
      network_frame
      (calc_network_input nio)
      (calc_network_input_len nio)
      (calc_network_output nio)
      (calc_network_output_len nio)
      (Ghost.reveal (calc_network_input_contents nio))
      (Ghost.reveal (calc_network_old_output nio)));
  fold (CalcCP.calc_network_frame_pre
    network_frame
    (calc_network_input nio)
    (calc_network_input_len nio)
    (calc_network_output nio)
    (calc_network_output_len nio)
    (Ghost.reveal (calc_network_input_contents nio))
    (Ghost.reveal (calc_network_old_output nio)));
  fold (calc_network_continuation srv cfg frame (Ghost.reveal log) network_frame);
  fold (calc_network_io_continuation srv ch frame (Ghost.reveal received) (Ghost.reveal sent) (Ghost.reveal log) nio);
  fold (PE.network_buffers
    (calc_network_input nio)
    (calc_network_input_len nio)
    (calc_network_output nio)
    (calc_network_output_len nio)
    (Ghost.reveal (calc_network_input_contents nio))
    (Ghost.reveal (calc_network_old_output nio)))
}

inline_for_extraction
fn calc_finish_network_action
  (srv:CalcCP.canonical_server)
  (cfg:calc_endpoint_config)
  (frame:CalcCP.calc_network_frame)
  (network_frame:CalcCP.calc_network_frame)
  (result:CPI.process_result)
  (input_contents:Ghost.erased TCP.bytes)
  (input_len:SZ.t)
  (old_out:Ghost.erased TCP.bytes)
  (out_contents:Ghost.erased TCP.bytes)
  (log0:Ghost.erased calc_log)
  (log1:Ghost.erased calc_log)
  (consumed:Ghost.erased TCP.bytes)
  (wire_outputs:Ghost.erased (list CalcP.calc_frame))
  (local_outputs:Ghost.erased (list unit))
requires
  calc_network_continuation srv cfg frame (Ghost.reveal log0) network_frame **
  CalcCP.calc_network_frame_post
    network_frame
    result
    (Ghost.reveal input_contents)
    input_len
    (Ghost.reveal old_out)
    (Ghost.reveal out_contents)
    (Ghost.reveal log0)
    (Ghost.reveal log1)
    (Ghost.reveal consumed)
    (Ghost.reveal wire_outputs)
    (Ghost.reveal local_outputs)
ensures calc_frame_ready srv cfg frame (Ghost.reveal log1)
{
  unfold (calc_network_continuation srv cfg frame (Ghost.reveal log0) network_frame);
  unfold (CalcCP.calc_network_frame_post
    network_frame
    result
    (Ghost.reveal input_contents)
    input_len
    (Ghost.reveal old_out)
    (Ghost.reveal out_contents)
    (Ghost.reveal log0)
    (Ghost.reveal log1)
    (Ghost.reveal consumed)
    (Ghost.reveal wire_outputs)
    (Ghost.reveal local_outputs));
  fold (calc_frame_ready srv cfg frame (Ghost.reveal log1))
}

inline_for_extraction
fn calc_prepare_network
  (srv:CalcCP.canonical_server)
  (cfg:calc_endpoint_config)
  (frame:CalcCP.calc_network_frame)
  (ch:TCP.channel)
  (network_frame:CalcCP.calc_network_frame)
  (received:Ghost.erased TCP.bytes)
  (sent:Ghost.erased TCP.bytes)
  (log:Ghost.erased calc_log)
requires
  calc_action_frame srv cfg frame (Ghost.reveal log) (PE.EndpointNeedInput network_frame) **
  calc_io_ready srv ch frame (Ghost.reveal received) (Ghost.reveal sent) (Ghost.reveal log)
returns nio:calc_network_io
ensures
  calc_network_io_continuation srv ch frame (Ghost.reveal received) (Ghost.reveal sent) (Ghost.reveal log) nio **
  PE.network_buffers
    (calc_network_input nio)
    (calc_network_input_len nio)
    (calc_network_output nio)
    (calc_network_output_len nio)
    (Ghost.reveal (calc_network_input_contents nio))
    (Ghost.reveal (calc_network_old_output nio)) **
  CalcCP.calc_network_frame_pre
    network_frame
    (calc_network_input nio)
    (calc_network_input_len nio)
    (calc_network_output nio)
    (calc_network_output_len nio)
    (Ghost.reveal (calc_network_input_contents nio))
    (Ghost.reveal (calc_network_old_output nio)) **
  calc_network_continuation srv cfg frame (Ghost.reveal log) network_frame **
  pure (
    CPI.buffers_wf
      (Ghost.reveal (calc_network_input_contents nio))
      (calc_network_input_len nio)
      (Ghost.reveal (calc_network_old_output nio))
      (calc_network_output_len nio))
{
  let nio = calc_prepare_network_io srv ch frame received sent log;
  calc_prepare_network_action
    srv
    cfg
    frame
    ch
    nio
    network_frame
    received
    sent
    log;
  nio
}

inline_for_extraction
fn calc_finish_network_io_observed
  (srv:CalcCP.canonical_server)
  (ch:TCP.channel)
  (frame:CalcCP.calc_network_frame)
  (nio:calc_network_io)
  (result:CPI.process_result)
  (received0:Ghost.erased TCP.bytes)
  (sent0:Ghost.erased TCP.bytes)
  (log0:Ghost.erased calc_log)
  (received1:Ghost.erased TCP.bytes)
  (sent1:Ghost.erased TCP.bytes)
  (log1:Ghost.erased calc_log)
  (out_contents:Ghost.erased TCP.bytes)
  (consumed:Ghost.erased TCP.bytes)
  (wire_outputs:Ghost.erased (list CalcP.calc_frame))
  (local_outputs:Ghost.erased (list unit))
requires
  calc_network_io_continuation srv ch frame (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal log0) nio **
  pts_to (calc_network_input nio) (Ghost.reveal (calc_network_input_contents nio)) **
  pts_to (calc_network_output nio) (Ghost.reveal out_contents) **
  pure (
    CPI.network_process_correct
      (CalcCP.calc_server_protocol_implementation.CPI.pi_system srv)
      (Ghost.reveal (calc_network_input_contents nio))
      (calc_network_input_len nio)
      (Ghost.reveal (calc_network_old_output nio))
      (Ghost.reveal out_contents)
      (calc_network_output_len nio)
      (Ghost.reveal received0)
      (Ghost.reveal sent0)
      (Ghost.reveal log0)
      result
      (Ghost.reveal received1)
      (Ghost.reveal sent1)
      (Ghost.reveal log1)
      (Ghost.reveal consumed)
      (Ghost.reveal wire_outputs)
      (Ghost.reveal local_outputs))
returns written:SZ.t
ensures
  calc_io_ready srv ch frame (Ghost.reveal received1) (Ghost.reveal sent1) (Ghost.reveal log1) **
  pure (written == result.CPI.process_produced_len)
{
  unfold (calc_network_io_continuation srv ch frame (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal log0) nio);
  CPI.lemma_network_process_sent_output_prefix
    (CalcCP.calc_server_protocol_implementation.CPI.pi_system srv)
    (Ghost.reveal (calc_network_input_contents nio))
    (calc_network_input_len nio)
    (Ghost.reveal (calc_network_old_output nio))
    (Ghost.reveal out_contents)
    (calc_network_output_len nio)
    (Ghost.reveal received0)
    (Ghost.reveal sent0)
    (Ghost.reveal log0)
    result
    (Ghost.reveal received1)
    (Ghost.reveal sent1)
    (Ghost.reveal log1)
    (Ghost.reveal consumed)
    (Ghost.reveal wire_outputs)
    (Ghost.reveal local_outputs);
  assert (pure (SZ.v result.CPI.process_produced_len <= Seq.length (Ghost.reveal out_contents)));
  let nwritten = TCP.write ch (calc_network_output nio) result.CPI.process_produced_len;
  assert (pure (nwritten == result.CPI.process_produced_len));
  rewrite
    (TCP.is_channel
      ch
      (Ghost.reveal nio.calc_nio_raw_received)
      (Seq.append
        (Ghost.reveal sent0)
        (if SZ.v nwritten <= Seq.length (Ghost.reveal out_contents)
         then Seq.slice (Ghost.reveal out_contents) 0 (SZ.v nwritten)
         else Seq.create 0 0uy)))
    as
    (TCP.is_channel
      ch
      (Ghost.reveal nio.calc_nio_raw_received)
      (Seq.append
        (Ghost.reveal sent0)
        (if SZ.v result.CPI.process_produced_len <= Seq.length (Ghost.reveal out_contents)
         then Seq.slice (Ghost.reveal out_contents) 0 (SZ.v result.CPI.process_produced_len)
         else Seq.create 0 0uy)));
  assert (pure (Seq.equal
    (Ghost.reveal sent1)
    (Seq.append
      (Ghost.reveal sent0)
      (CPI.output_prefix (Ghost.reveal out_contents) result.CPI.process_produced_len))));
  rewrite
    (TCP.is_channel
      ch
      (Ghost.reveal nio.calc_nio_raw_received)
      (Seq.append
        (Ghost.reveal sent0)
        (if SZ.v result.CPI.process_produced_len <= Seq.length (Ghost.reveal out_contents)
         then Seq.slice (Ghost.reveal out_contents) 0 (SZ.v result.CPI.process_produced_len)
         else Seq.create 0 0uy)))
    as
    (TCP.is_channel ch (Ghost.reveal nio.calc_nio_raw_received) (Ghost.reveal sent1));
  assert (pure (Seq.length (Ghost.reveal out_contents) == 5));
  rewrite
    (pts_to (calc_network_input nio) (Ghost.reveal (calc_network_input_contents nio)))
    as
    (pts_to (Vec.vec_to_array frame.CalcCP.calc_network_req) (Ghost.reveal (calc_network_input_contents nio)));
  rewrite
    (pts_to (calc_network_output nio) (Ghost.reveal out_contents))
    as
    (pts_to (Vec.vec_to_array frame.CalcCP.calc_network_resp) (Ghost.reveal out_contents));
  Vec.to_vec_pts_to frame.CalcCP.calc_network_req;
  Vec.to_vec_pts_to frame.CalcCP.calc_network_resp;
  fold (calc_io_ready srv ch frame (Ghost.reveal received1) (Ghost.reveal sent1) (Ghost.reveal log1));
  nwritten
}

noextract
fn calc_finish_network_io
  (srv:CalcCP.canonical_server)
  (ch:TCP.channel)
  (frame:CalcCP.calc_network_frame)
  (nio:calc_network_io)
  (result:CPI.process_result)
  (received0:Ghost.erased TCP.bytes)
  (sent0:Ghost.erased TCP.bytes)
  (log0:Ghost.erased calc_log)
  (received1:Ghost.erased TCP.bytes)
  (sent1:Ghost.erased TCP.bytes)
  (log1:Ghost.erased calc_log)
  (out_contents:Ghost.erased TCP.bytes)
  (consumed:Ghost.erased TCP.bytes)
  (wire_outputs:Ghost.erased (list CalcP.calc_frame))
  (local_outputs:Ghost.erased (list unit))
requires
  calc_network_io_continuation srv ch frame (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal log0) nio **
  pts_to (calc_network_input nio) (Ghost.reveal (calc_network_input_contents nio)) **
  pts_to (calc_network_output nio) (Ghost.reveal out_contents) **
  pure (
    CPI.network_process_correct
      (CalcCP.calc_server_protocol_implementation.CPI.pi_system srv)
      (Ghost.reveal (calc_network_input_contents nio))
      (calc_network_input_len nio)
      (Ghost.reveal (calc_network_old_output nio))
      (Ghost.reveal out_contents)
      (calc_network_output_len nio)
      (Ghost.reveal received0)
      (Ghost.reveal sent0)
      (Ghost.reveal log0)
      result
      (Ghost.reveal received1)
      (Ghost.reveal sent1)
      (Ghost.reveal log1)
      (Ghost.reveal consumed)
      (Ghost.reveal wire_outputs)
      (Ghost.reveal local_outputs))
ensures calc_io_ready srv ch frame (Ghost.reveal received1) (Ghost.reveal sent1) (Ghost.reveal log1)
{
  let _written =
    calc_finish_network_io_observed
      srv
      ch
      frame
      nio
      result
      received0
      sent0
      log0
      received1
      sent1
      log1
      out_contents
      consumed
      wire_outputs
      local_outputs;
  ()
}

noeq
type calc_local_io = {
  calc_lio_output: array U8.t;
  calc_lio_old_output: Ghost.erased TCP.bytes;
  calc_lio_raw_received: Ghost.erased TCP.bytes;
  calc_lio_req_contents: Ghost.erased TCP.bytes;
}

let calc_local_io_continuation
  (_srv:CalcCP.canonical_server)
  (ch:TCP.channel)
  (frame:CalcCP.calc_network_frame)
  (_received:TCP.bytes)
  (sent:TCP.bytes)
  (_log:calc_log)
  (_ev:CalcP.calc_frame_local_event)
  (lio:calc_local_io)
  : slprop =
  TCP.is_channel ch (Ghost.reveal lio.calc_lio_raw_received) sent **
  Vec.pts_to frame.CalcCP.calc_network_req (Ghost.reveal lio.calc_lio_req_contents) **
  pure (
    lio.calc_lio_output == Vec.vec_to_array frame.CalcCP.calc_network_resp /\
    Seq.length (Ghost.reveal lio.calc_lio_req_contents) == 5 /\
    Seq.length (Ghost.reveal lio.calc_lio_old_output) == 5 /\
    Vec.length frame.CalcCP.calc_network_req == 5 /\
    Vec.length frame.CalcCP.calc_network_resp == 5 /\
    Vec.is_full_vec frame.CalcCP.calc_network_req /\
    Vec.is_full_vec frame.CalcCP.calc_network_resp)

let calc_local_output (lio:calc_local_io) : array U8.t =
  lio.calc_lio_output

let calc_local_output_len (_lio:calc_local_io) : SZ.t =
  5sz

let calc_local_old_output (lio:calc_local_io) : Ghost.erased TCP.bytes =
  lio.calc_lio_old_output

fn calc_prepare_local_io
  (srv:CalcCP.canonical_server)
  (ch:TCP.channel)
  (frame:CalcCP.calc_network_frame)
  (ev:CalcP.calc_frame_local_event)
  (received:Ghost.erased TCP.bytes)
  (sent:Ghost.erased TCP.bytes)
  (log:Ghost.erased calc_log)
requires calc_io_ready srv ch frame (Ghost.reveal received) (Ghost.reveal sent) (Ghost.reveal log)
returns lio:calc_local_io
ensures
  calc_local_io_continuation srv ch frame (Ghost.reveal received) (Ghost.reveal sent) (Ghost.reveal log) ev lio **
  PE.local_output_buffer
    (calc_local_output lio)
    (calc_local_output_len lio)
    (Ghost.reveal (calc_local_old_output lio))
{
  unfold (calc_io_ready srv ch frame (Ghost.reveal received) (Ghost.reveal sent) (Ghost.reveal log));
  with raw_received req_bytes resp_bytes. _;
  Vec.to_array_pts_to frame.CalcCP.calc_network_resp;
  let reqe = Ghost.hide req_bytes;
  let olde = Ghost.hide resp_bytes;
  let rawe = Ghost.hide raw_received;
  let lio = {
    calc_lio_output = Vec.vec_to_array frame.CalcCP.calc_network_resp;
    calc_lio_old_output = olde;
    calc_lio_raw_received = rawe;
    calc_lio_req_contents = reqe;
  };
  assert (pure (Ghost.reveal reqe == req_bytes));
  assert (pure (Ghost.reveal olde == resp_bytes));
  assert (pure (Ghost.reveal rawe == raw_received));
  assert (pure (lio.calc_lio_raw_received == rawe));
  rewrite
    (TCP.is_channel ch raw_received (Ghost.reveal sent))
    as
    (TCP.is_channel ch (Ghost.reveal rawe) (Ghost.reveal sent));
  rewrite
    (TCP.is_channel ch (Ghost.reveal rawe) (Ghost.reveal sent))
    as
    (TCP.is_channel ch (Ghost.reveal lio.calc_lio_raw_received) (Ghost.reveal sent));
  fold (calc_local_io_continuation srv ch frame (Ghost.reveal received) (Ghost.reveal sent) (Ghost.reveal log) ev lio);
  rewrite
    (pts_to (Vec.vec_to_array frame.CalcCP.calc_network_resp) resp_bytes)
    as
    (pts_to (calc_local_output lio) (Ghost.reveal (calc_local_old_output lio)));
  fold (PE.local_output_buffer
    (calc_local_output lio)
    (calc_local_output_len lio)
    (Ghost.reveal (calc_local_old_output lio)));
  lio
}

fn calc_prepare_local_action
  (srv:CalcCP.canonical_server)
  (cfg:calc_endpoint_config)
  (frame:CalcCP.calc_network_frame)
  (ch:TCP.channel)
  (lio:calc_local_io)
  (ev:CalcP.calc_frame_local_event)
  (local_frame:CalcCP.calc_local_frame)
  (received:Ghost.erased TCP.bytes)
  (sent:Ghost.erased TCP.bytes)
  (log:Ghost.erased calc_log)
requires
  calc_action_frame srv cfg frame (Ghost.reveal log) (PE.EndpointLocal ev local_frame) **
  calc_local_io_continuation srv ch frame (Ghost.reveal received) (Ghost.reveal sent) (Ghost.reveal log) ev lio **
  PE.local_output_buffer
    (calc_local_output lio)
    (calc_local_output_len lio)
    (Ghost.reveal (calc_local_old_output lio))
ensures
  CalcCP.calc_local_frame_pre
    ev
    local_frame
    (Ghost.reveal log)
    (calc_local_output lio)
    (calc_local_output_len lio)
    (Ghost.reveal (calc_local_old_output lio)) **
  calc_local_continuation srv cfg frame (Ghost.reveal log) ev local_frame **
  calc_local_io_continuation srv ch frame (Ghost.reveal received) (Ghost.reveal sent) (Ghost.reveal log) ev lio **
  PE.local_output_buffer
    (calc_local_output lio)
    (calc_local_output_len lio)
    (Ghost.reveal (calc_local_old_output lio))
{
  unfold (calc_action_frame srv cfg frame (Ghost.reveal log) (PE.EndpointLocal ev local_frame));
  assert (pure False);
  fold (CalcCP.calc_local_frame_pre
    ev
    local_frame
    (Ghost.reveal log)
    (calc_local_output lio)
    (calc_local_output_len lio)
    (Ghost.reveal (calc_local_old_output lio)));
  fold (calc_local_continuation srv cfg frame (Ghost.reveal log) ev local_frame)
}

fn calc_finish_local_action
  (srv:CalcCP.canonical_server)
  (cfg:calc_endpoint_config)
  (frame:CalcCP.calc_network_frame)
  (ev:CalcP.calc_frame_local_event)
  (local_frame:CalcCP.calc_local_frame)
  (result:CPI.process_result)
  (old_out:Ghost.erased TCP.bytes)
  (out_contents:Ghost.erased TCP.bytes)
  (log0:Ghost.erased calc_log)
  (log1:Ghost.erased calc_log)
  (wire_outputs:Ghost.erased (list CalcP.calc_frame))
  (local_outputs:Ghost.erased (list unit))
requires
  calc_local_continuation srv cfg frame (Ghost.reveal log0) ev local_frame **
  CalcCP.calc_local_frame_post
    ev
    local_frame
    result
    (Ghost.reveal old_out)
    (Ghost.reveal out_contents)
    (Ghost.reveal log0)
    (Ghost.reveal log1)
    (Ghost.reveal wire_outputs)
    (Ghost.reveal local_outputs)
ensures calc_frame_ready srv cfg frame (Ghost.reveal log1)
{
  unfold (calc_local_continuation srv cfg frame (Ghost.reveal log0) ev local_frame);
  unfold (CalcCP.calc_local_frame_post
    ev
    local_frame
    result
    (Ghost.reveal old_out)
    (Ghost.reveal out_contents)
    (Ghost.reveal log0)
    (Ghost.reveal log1)
    (Ghost.reveal wire_outputs)
    (Ghost.reveal local_outputs));
  fold (calc_frame_ready srv cfg frame (Ghost.reveal log1))
}

fn calc_prepare_local
  (srv:CalcCP.canonical_server)
  (cfg:calc_endpoint_config)
  (frame:CalcCP.calc_network_frame)
  (ch:TCP.channel)
  (ev:CalcP.calc_frame_local_event)
  (local_frame:CalcCP.calc_local_frame)
  (received:Ghost.erased TCP.bytes)
  (sent:Ghost.erased TCP.bytes)
  (log:Ghost.erased calc_log)
requires
  calc_action_frame srv cfg frame (Ghost.reveal log) (PE.EndpointLocal ev local_frame) **
  calc_io_ready srv ch frame (Ghost.reveal received) (Ghost.reveal sent) (Ghost.reveal log)
returns lio:calc_local_io
ensures
  calc_local_io_continuation srv ch frame (Ghost.reveal received) (Ghost.reveal sent) (Ghost.reveal log) ev lio **
  PE.local_output_buffer
    (calc_local_output lio)
    (calc_local_output_len lio)
    (Ghost.reveal (calc_local_old_output lio)) **
  CalcCP.calc_local_frame_pre
    ev
    local_frame
    (Ghost.reveal log)
    (calc_local_output lio)
    (calc_local_output_len lio)
    (Ghost.reveal (calc_local_old_output lio)) **
  calc_local_continuation srv cfg frame (Ghost.reveal log) ev local_frame
{
  let lio = calc_prepare_local_io srv ch frame ev received sent log;
  calc_prepare_local_action
    srv
    cfg
    frame
    ch
    lio
    ev
    local_frame
    received
    sent
    log;
  lio
}

fn calc_finish_local_io
  (srv:CalcCP.canonical_server)
  (ch:TCP.channel)
  (frame:CalcCP.calc_network_frame)
  (lio:calc_local_io)
  (ev:CalcP.calc_frame_local_event)
  (result:CPI.process_result)
  (received0:Ghost.erased TCP.bytes)
  (sent0:Ghost.erased TCP.bytes)
  (log0:Ghost.erased calc_log)
  (received1:Ghost.erased TCP.bytes)
  (sent1:Ghost.erased TCP.bytes)
  (log1:Ghost.erased calc_log)
  (out_contents:Ghost.erased TCP.bytes)
  (wire_outputs:Ghost.erased (list CalcP.calc_frame))
  (local_outputs:Ghost.erased (list unit))
requires
  calc_local_io_continuation srv ch frame (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal log0) ev lio **
  pts_to (calc_local_output lio) (Ghost.reveal out_contents) **
  pure (
    CPI.local_process_correct
      (CalcCP.calc_server_protocol_implementation.CPI.pi_system srv)
      ev
      (Ghost.reveal (calc_local_old_output lio))
      (Ghost.reveal out_contents)
      (calc_local_output_len lio)
      (Ghost.reveal received0)
      (Ghost.reveal sent0)
      (Ghost.reveal log0)
      result
      (Ghost.reveal received1)
      (Ghost.reveal sent1)
      (Ghost.reveal log1)
      (Ghost.reveal wire_outputs)
      (Ghost.reveal local_outputs))
ensures calc_io_ready srv ch frame (Ghost.reveal received1) (Ghost.reveal sent1) (Ghost.reveal log1)
{
  unfold (calc_local_io_continuation srv ch frame (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal log0) ev lio);
  CPI.lemma_local_process_sent_output_prefix
    (CalcCP.calc_server_protocol_implementation.CPI.pi_system srv)
    ev
    (Ghost.reveal (calc_local_old_output lio))
    (Ghost.reveal out_contents)
    (calc_local_output_len lio)
    (Ghost.reveal received0)
    (Ghost.reveal sent0)
    (Ghost.reveal log0)
    result
    (Ghost.reveal received1)
    (Ghost.reveal sent1)
    (Ghost.reveal log1)
    (Ghost.reveal wire_outputs)
    (Ghost.reveal local_outputs);
  assert (pure (SZ.v result.CPI.process_produced_len <= Seq.length (Ghost.reveal out_contents)));
  let nwritten = TCP.write ch (calc_local_output lio) result.CPI.process_produced_len;
  assert (pure (nwritten == result.CPI.process_produced_len));
  rewrite
    (TCP.is_channel
      ch
      (Ghost.reveal lio.calc_lio_raw_received)
      (Seq.append
        (Ghost.reveal sent0)
        (if SZ.v nwritten <= Seq.length (Ghost.reveal out_contents)
         then Seq.slice (Ghost.reveal out_contents) 0 (SZ.v nwritten)
         else Seq.create 0 0uy)))
    as
    (TCP.is_channel
      ch
      (Ghost.reveal lio.calc_lio_raw_received)
      (Seq.append
        (Ghost.reveal sent0)
        (if SZ.v result.CPI.process_produced_len <= Seq.length (Ghost.reveal out_contents)
         then Seq.slice (Ghost.reveal out_contents) 0 (SZ.v result.CPI.process_produced_len)
         else Seq.create 0 0uy)));
  rewrite
    (TCP.is_channel
      ch
      (Ghost.reveal lio.calc_lio_raw_received)
      (Seq.append
        (Ghost.reveal sent0)
        (if SZ.v result.CPI.process_produced_len <= Seq.length (Ghost.reveal out_contents)
         then Seq.slice (Ghost.reveal out_contents) 0 (SZ.v result.CPI.process_produced_len)
         else Seq.create 0 0uy)))
    as
    (TCP.is_channel ch (Ghost.reveal lio.calc_lio_raw_received) (Ghost.reveal sent1));
  assert (pure (Seq.length (Ghost.reveal out_contents) == 5));
  rewrite
    (pts_to (calc_local_output lio) (Ghost.reveal out_contents))
    as
    (pts_to (Vec.vec_to_array frame.CalcCP.calc_network_resp) (Ghost.reveal out_contents));
  Vec.to_vec_pts_to frame.CalcCP.calc_network_resp;
  fold (calc_io_ready srv ch frame (Ghost.reveal received1) (Ghost.reveal sent1) (Ghost.reveal log1))
}

noextract
let calc_protocol_endpoint
  : PE.protocol_endpoint
      CalcCP.canonical_server
      calc_log
      CalcP.calc_frame
      CalcP.calc_frame_local_event
      unit
      CalcCP.calc_server_protocol_implementation
  =
  {
    PE.pe_config = calc_endpoint_config;
    PE.pe_frame = CalcCP.calc_network_frame;
    PE.pe_frame_ready = calc_frame_ready;
    PE.pe_io_ready = calc_io_ready;
    PE.pe_action_frame = calc_action_frame;
    PE.pe_network_continuation = calc_network_continuation;
    PE.pe_local_continuation = calc_local_continuation;
    PE.pe_next_action = calc_next_action;
    PE.pe_cancel_action = calc_cancel_action;
    PE.pe_finish_network_action = calc_finish_network_action;
    PE.pe_finish_local_action = calc_finish_local_action;
    PE.pe_network_io = calc_network_io;
    PE.pe_network_io_continuation = calc_network_io_continuation;
    PE.pe_network_input = calc_network_input;
    PE.pe_network_input_len = calc_network_input_len;
    PE.pe_network_output = calc_network_output;
    PE.pe_network_output_len = calc_network_output_len;
    PE.pe_network_input_contents = calc_network_input_contents;
    PE.pe_network_old_output = calc_network_old_output;
    PE.pe_prepare_network = calc_prepare_network;
    PE.pe_finish_network_io = calc_finish_network_io;
    PE.pe_local_io = calc_local_io;
    PE.pe_local_io_continuation = calc_local_io_continuation;
    PE.pe_local_output = calc_local_output;
    PE.pe_local_output_len = calc_local_output_len;
    PE.pe_local_old_output = calc_local_old_output;
    PE.pe_prepare_local = calc_prepare_local;
    PE.pe_finish_local_io = calc_finish_local_io;
  }

fn free_canonical_server
  (srv:CalcCP.canonical_server)
  (#received:erased TCP.bytes)
  (#sent:erased TCP.bytes)
  (#log:erased calc_log)
requires
  CalcCP.canonical_server_exactly srv received sent log **
  pure (
    Vec.is_full_vec srv.CalcCP.canonical_server_state.stack /\
    Vec.is_full_vec srv.CalcCP.canonical_server_state.size)
ensures emp
{
  unfold (CalcCP.canonical_server_exactly srv received sent log);
  unfold (server_exactly srv.CalcCP.canonical_server_state log);
  with stack_bytes size_seq. _;
  Vec.free srv.CalcCP.canonical_server_state.stack;
  Vec.free srv.CalcCP.canonical_server_state.size;
  drop_ (MR.pts_to srv.CalcCP.canonical_server_state.ghost_log #1.0R log);
  drop_ (MR.pts_to srv.CalcCP.canonical_server_progress #1.0R log)
}

noextract
fn calc_drive_once
  (srv:CalcCP.canonical_server)
  (frame:CalcCP.calc_network_frame)
  (ch:TCP.channel)
  (received:Ghost.erased TCP.bytes)
  (sent:Ghost.erased TCP.bytes)
  (log:Ghost.erased calc_log)
requires
  CalcCP.calc_server_protocol_implementation.CPI.pi_invariant
    srv
    (Ghost.reveal received)
    (Ghost.reveal sent)
    (Ghost.reveal log) **
  calc_protocol_endpoint.PE.pe_frame_ready
    srv
    ()
    frame
    (Ghost.reveal log) **
  calc_protocol_endpoint.PE.pe_io_ready
    srv
    ch
    frame
    (Ghost.reveal received)
    (Ghost.reveal sent)
    (Ghost.reveal log)
returns result:PD.driver_result
ensures
  (match result.PD.driver_status with
  | PD.DriverNetworkStep
  | PD.DriverLocalStep
  | PD.DriverFailed ->
    exists* (received1:Ghost.erased TCP.bytes)
            (sent1:Ghost.erased TCP.bytes)
            (log1:Ghost.erased calc_log).
      CalcCP.calc_server_protocol_implementation.CPI.pi_invariant
        srv
        (Ghost.reveal received1)
        (Ghost.reveal sent1)
        (Ghost.reveal log1) **
      calc_protocol_endpoint.PE.pe_frame_ready
        srv
        ()
        frame
        (Ghost.reveal log1) **
      calc_protocol_endpoint.PE.pe_io_ready
        srv
        ch
        frame
        (Ghost.reveal received1)
        (Ghost.reveal sent1)
        (Ghost.reveal log1)
  | PD.DriverDone ->
      CalcCP.calc_server_protocol_implementation.CPI.pi_invariant
        srv
        (Ghost.reveal received)
        (Ghost.reveal sent)
        (Ghost.reveal log) **
      calc_protocol_endpoint.PE.pe_frame_ready
        srv
        ()
        frame
        (Ghost.reveal log) **
      calc_protocol_endpoint.PE.pe_io_ready
        srv
        ch
        frame
        (Ghost.reveal received)
        (Ghost.reveal sent)
        (Ghost.reveal log))
{
  rewrite
    (CalcCP.calc_server_protocol_implementation.CPI.pi_invariant
      srv
      (Ghost.reveal received)
      (Ghost.reveal sent)
      (Ghost.reveal log))
    as
    (CalcCP.canonical_server_exactly
      srv
      (Ghost.reveal received)
      (Ghost.reveal sent)
      (Ghost.reveal log));
  rewrite
    (calc_protocol_endpoint.PE.pe_frame_ready srv () frame (Ghost.reveal log))
    as
    (calc_frame_ready srv () frame (Ghost.reveal log));
  rewrite
    (calc_protocol_endpoint.PE.pe_io_ready
      srv
      ch
      frame
      (Ghost.reveal received)
      (Ghost.reveal sent)
      (Ghost.reveal log))
    as
    (calc_io_ready
      srv
      ch
      frame
      (Ghost.reveal received)
      (Ghost.reveal sent)
      (Ghost.reveal log));
  let action = calc_next_action srv () frame received sent log;
  match action {
    PE.EndpointNeedInput network_frame -> {
      let nio =
        calc_prepare_network
          srv
          ()
          frame
          ch
          network_frame
          received
          sent
          log;
      let process_result =
        CalcCP.calc_process_network
          srv
          network_frame
          (calc_network_input nio)
          (calc_network_input_len nio)
          (calc_network_output nio)
          (calc_network_output_len nio)
          received
          sent
          log
          (calc_network_input_contents nio)
          (calc_network_old_output nio);
      with received1 sent1 log1 out_contents consumed wire_outputs local_outputs.
        assert (
          CalcCP.canonical_server_exactly
            srv
            (Ghost.reveal received1)
            (Ghost.reveal sent1)
            (Ghost.reveal log1) **
          CalcCP.calc_network_frame_post
            network_frame
            process_result
            (Ghost.reveal (calc_network_input_contents nio))
            (calc_network_input_len nio)
            (Ghost.reveal (calc_network_old_output nio))
            out_contents
            (Ghost.reveal log)
            (Ghost.reveal log1)
            consumed
            wire_outputs
            local_outputs **
          pts_to (calc_network_input nio) (Ghost.reveal (calc_network_input_contents nio)) **
          pts_to (calc_network_output nio) out_contents **
          pure (
            CPI.network_process_correct
              (CalcCP.calc_server_protocol_implementation.CPI.pi_system srv)
              (Ghost.reveal (calc_network_input_contents nio))
              (calc_network_input_len nio)
              (Ghost.reveal (calc_network_old_output nio))
              out_contents
              (calc_network_output_len nio)
              (Ghost.reveal received)
              (Ghost.reveal sent)
              (Ghost.reveal log)
              process_result
              (Ghost.reveal received1)
              (Ghost.reveal sent1)
              (Ghost.reveal log1)
              consumed
              wire_outputs
              local_outputs));
      let out_contentse = Ghost.hide out_contents;
      let consumede = Ghost.hide consumed;
      let wire_outputse = Ghost.hide wire_outputs;
      let local_outputse = Ghost.hide local_outputs;
      assert (pure (Ghost.reveal out_contentse == out_contents));
      assert (pure (Ghost.reveal consumede == consumed));
      assert (pure (Ghost.reveal wire_outputse == wire_outputs));
      assert (pure (Ghost.reveal local_outputse == local_outputs));
      rewrite
        (CalcCP.calc_network_frame_post
          network_frame
          process_result
          (Ghost.reveal (calc_network_input_contents nio))
          (calc_network_input_len nio)
          (Ghost.reveal (calc_network_old_output nio))
          out_contents
          (Ghost.reveal log)
          (Ghost.reveal log1)
          consumed
          wire_outputs
          local_outputs)
        as
        (CalcCP.calc_network_frame_post
          network_frame
          process_result
          (Ghost.reveal (calc_network_input_contents nio))
          (calc_network_input_len nio)
          (Ghost.reveal (calc_network_old_output nio))
          (Ghost.reveal out_contentse)
          (Ghost.reveal log)
          (Ghost.reveal log1)
          (Ghost.reveal consumede)
          (Ghost.reveal wire_outputse)
          (Ghost.reveal local_outputse));
      calc_finish_network_action
        srv
        ()
        frame
        network_frame
        process_result
        (calc_network_input_contents nio)
        (calc_network_input_len nio)
        (calc_network_old_output nio)
        out_contentse
        log
        log1
        consumede
        wire_outputse
        local_outputse;
      let nwritten =
        calc_finish_network_io_observed
          srv
          ch
          frame
          nio
          process_result
          received
          sent
          log
          received1
          sent1
          log1
          out_contentse
          consumede
          wire_outputse
          local_outputse;
      rewrite
        (CalcCP.canonical_server_exactly
          srv
          (Ghost.reveal received1)
          (Ghost.reveal sent1)
          (Ghost.reveal log1))
        as
        (CalcCP.calc_server_protocol_implementation.CPI.pi_invariant
          srv
          (Ghost.reveal received1)
          (Ghost.reveal sent1)
          (Ghost.reveal log1));
      rewrite
        (calc_frame_ready srv () frame (Ghost.reveal log1))
        as
        (calc_protocol_endpoint.PE.pe_frame_ready srv () frame (Ghost.reveal log1));
      rewrite
        (calc_io_ready
          srv
          ch
          frame
          (Ghost.reveal received1)
          (Ghost.reveal sent1)
          (Ghost.reveal log1))
        as
        (calc_protocol_endpoint.PE.pe_io_ready
          srv
          ch
          frame
          (Ghost.reveal received1)
          (Ghost.reveal sent1)
          (Ghost.reveal log1));
      let status = PD.network_driver_status process_result;
      assert (pure (status == PD.DriverNetworkStep \/ status == PD.DriverFailed));
      match status {
        PD.DriverNetworkStep -> {
          ({
            PD.driver_status = PD.DriverNetworkStep;
            PD.driver_process_result = Some process_result;
          })
        }
        PD.DriverFailed -> {
          ({
            PD.driver_status = PD.DriverFailed;
            PD.driver_process_result = Some process_result;
          })
        }
        PD.DriverLocalStep -> {
          ({
            PD.driver_status = PD.DriverFailed;
            PD.driver_process_result = Some process_result;
          })
        }
        PD.DriverDone -> {
          ({
            PD.driver_status = PD.DriverFailed;
            PD.driver_process_result = Some process_result;
          })
        }
      }
    }
    PE.EndpointLocal ev local_frame -> {
      calc_cancel_action srv () frame log (PE.EndpointLocal ev local_frame);
      rewrite
        (CalcCP.canonical_server_exactly
          srv
          (Ghost.reveal received)
          (Ghost.reveal sent)
          (Ghost.reveal log))
        as
        (CalcCP.calc_server_protocol_implementation.CPI.pi_invariant
          srv
          (Ghost.reveal received)
          (Ghost.reveal sent)
          (Ghost.reveal log));
      rewrite
        (calc_frame_ready srv () frame (Ghost.reveal log))
        as
        (calc_protocol_endpoint.PE.pe_frame_ready srv () frame (Ghost.reveal log));
      rewrite
        (calc_io_ready
          srv
          ch
          frame
          (Ghost.reveal received)
          (Ghost.reveal sent)
          (Ghost.reveal log))
        as
        (calc_protocol_endpoint.PE.pe_io_ready
          srv
          ch
          frame
          (Ghost.reveal received)
          (Ghost.reveal sent)
          (Ghost.reveal log));
      ({
        PD.driver_status = PD.DriverFailed;
        PD.driver_process_result = None;
      })
    }
    PE.EndpointDone -> {
      calc_cancel_action srv () frame log PE.EndpointDone;
      rewrite
        (CalcCP.canonical_server_exactly
          srv
          (Ghost.reveal received)
          (Ghost.reveal sent)
          (Ghost.reveal log))
        as
        (CalcCP.calc_server_protocol_implementation.CPI.pi_invariant
          srv
          (Ghost.reveal received)
          (Ghost.reveal sent)
          (Ghost.reveal log));
      rewrite
        (calc_frame_ready srv () frame (Ghost.reveal log))
        as
        (calc_protocol_endpoint.PE.pe_frame_ready srv () frame (Ghost.reveal log));
      rewrite
        (calc_io_ready
          srv
          ch
          frame
          (Ghost.reveal received)
          (Ghost.reveal sent)
          (Ghost.reveal log))
        as
        (calc_protocol_endpoint.PE.pe_io_ready
          srv
          ch
          frame
          (Ghost.reveal received)
          (Ghost.reveal sent)
          (Ghost.reveal log));
      ({
        PD.driver_status = PD.DriverDone;
        PD.driver_process_result = None;
      })
    }
    PE.EndpointFailed -> {
      calc_cancel_action srv () frame log PE.EndpointFailed;
      rewrite
        (CalcCP.canonical_server_exactly
          srv
          (Ghost.reveal received)
          (Ghost.reveal sent)
          (Ghost.reveal log))
        as
        (CalcCP.calc_server_protocol_implementation.CPI.pi_invariant
          srv
          (Ghost.reveal received)
          (Ghost.reveal sent)
          (Ghost.reveal log));
      rewrite
        (calc_frame_ready srv () frame (Ghost.reveal log))
        as
        (calc_protocol_endpoint.PE.pe_frame_ready srv () frame (Ghost.reveal log));
      rewrite
        (calc_io_ready
          srv
          ch
          frame
          (Ghost.reveal received)
          (Ghost.reveal sent)
          (Ghost.reveal log))
        as
        (calc_protocol_endpoint.PE.pe_io_ready
          srv
          ch
          frame
          (Ghost.reveal received)
          (Ghost.reveal sent)
          (Ghost.reveal log));
      ({
        PD.driver_status = PD.DriverFailed;
        PD.driver_process_result = None;
      })
    }
  }
}

inline_for_extraction
fn calc_drive_once_network
  (srv:CalcCP.canonical_server)
  (frame:CalcCP.calc_network_frame)
  (ch:TCP.channel)
  (received:Ghost.erased TCP.bytes)
  (sent:Ghost.erased TCP.bytes)
  (log:Ghost.erased calc_log)
requires
  CalcCP.calc_server_protocol_implementation.CPI.pi_invariant
    srv
    (Ghost.reveal received)
    (Ghost.reveal sent)
    (Ghost.reveal log) **
  calc_protocol_endpoint.PE.pe_frame_ready
    srv
    ()
    frame
    (Ghost.reveal log) **
  calc_protocol_endpoint.PE.pe_io_ready
    srv
    ch
    frame
    (Ghost.reveal received)
    (Ghost.reveal sent)
    (Ghost.reveal log)
returns result:calc_driver_result
ensures
  exists* (received1:Ghost.erased TCP.bytes)
          (sent1:Ghost.erased TCP.bytes)
          (log1:Ghost.erased calc_log).
    CalcCP.calc_server_protocol_implementation.CPI.pi_invariant
      srv
      (Ghost.reveal received1)
      (Ghost.reveal sent1)
      (Ghost.reveal log1) **
    calc_protocol_endpoint.PE.pe_frame_ready
      srv
      ()
      frame
      (Ghost.reveal log1) **
    calc_protocol_endpoint.PE.pe_io_ready
      srv
      ch
      frame
      (Ghost.reveal received1)
      (Ghost.reveal sent1)
      (Ghost.reveal log1)
{
  rewrite
    (CalcCP.calc_server_protocol_implementation.CPI.pi_invariant
      srv
      (Ghost.reveal received)
      (Ghost.reveal sent)
      (Ghost.reveal log))
    as
    (CalcCP.canonical_server_exactly
      srv
      (Ghost.reveal received)
      (Ghost.reveal sent)
      (Ghost.reveal log));
  rewrite
    (calc_protocol_endpoint.PE.pe_frame_ready srv () frame (Ghost.reveal log))
    as
    (calc_frame_ready srv () frame (Ghost.reveal log));
  rewrite
    (calc_protocol_endpoint.PE.pe_io_ready
      srv
      ch
      frame
      (Ghost.reveal received)
      (Ghost.reveal sent)
      (Ghost.reveal log))
    as
    (calc_io_ready
      srv
      ch
      frame
      (Ghost.reveal received)
      (Ghost.reveal sent)
      (Ghost.reveal log));
  unfold (calc_frame_ready srv () frame (Ghost.reveal log));
  fold (calc_action_frame srv () frame (Ghost.reveal log) (PE.EndpointNeedInput frame));
  let nio =
    calc_prepare_network
      srv
      ()
      frame
      ch
      frame
      received
      sent
      log;
  let process_result =
    CalcCP.calc_process_network
      srv
      frame
      (calc_network_input nio)
      (calc_network_input_len nio)
      (calc_network_output nio)
      (calc_network_output_len nio)
      received
      sent
      log
      (calc_network_input_contents nio)
      (calc_network_old_output nio);
  with received1 sent1 log1 out_contents consumed wire_outputs local_outputs.
    assert (
      CalcCP.canonical_server_exactly
        srv
        (Ghost.reveal received1)
        (Ghost.reveal sent1)
        (Ghost.reveal log1) **
      CalcCP.calc_network_frame_post
        frame
        process_result
        (Ghost.reveal (calc_network_input_contents nio))
        (calc_network_input_len nio)
        (Ghost.reveal (calc_network_old_output nio))
        out_contents
        (Ghost.reveal log)
        (Ghost.reveal log1)
        consumed
        wire_outputs
        local_outputs **
      pts_to (calc_network_input nio) (Ghost.reveal (calc_network_input_contents nio)) **
      pts_to (calc_network_output nio) out_contents **
      pure (
        CPI.network_process_correct
          (CalcCP.calc_server_protocol_implementation.CPI.pi_system srv)
          (Ghost.reveal (calc_network_input_contents nio))
          (calc_network_input_len nio)
          (Ghost.reveal (calc_network_old_output nio))
          out_contents
          (calc_network_output_len nio)
          (Ghost.reveal received)
          (Ghost.reveal sent)
          (Ghost.reveal log)
          process_result
          (Ghost.reveal received1)
          (Ghost.reveal sent1)
          (Ghost.reveal log1)
          consumed
          wire_outputs
          local_outputs));
  let out_contentse = Ghost.hide out_contents;
  let consumede = Ghost.hide consumed;
  let wire_outputse = Ghost.hide wire_outputs;
  let local_outputse = Ghost.hide local_outputs;
  assert (pure (Ghost.reveal out_contentse == out_contents));
  assert (pure (Ghost.reveal consumede == consumed));
  assert (pure (Ghost.reveal wire_outputse == wire_outputs));
  assert (pure (Ghost.reveal local_outputse == local_outputs));
  rewrite
    (CalcCP.calc_network_frame_post
      frame
      process_result
      (Ghost.reveal (calc_network_input_contents nio))
      (calc_network_input_len nio)
      (Ghost.reveal (calc_network_old_output nio))
      out_contents
      (Ghost.reveal log)
      (Ghost.reveal log1)
      consumed
      wire_outputs
      local_outputs)
    as
    (CalcCP.calc_network_frame_post
      frame
      process_result
      (Ghost.reveal (calc_network_input_contents nio))
      (calc_network_input_len nio)
      (Ghost.reveal (calc_network_old_output nio))
      (Ghost.reveal out_contentse)
      (Ghost.reveal log)
      (Ghost.reveal log1)
      (Ghost.reveal consumede)
      (Ghost.reveal wire_outputse)
      (Ghost.reveal local_outputse));
  calc_finish_network_action
    srv
    ()
    frame
    frame
    process_result
    (calc_network_input_contents nio)
    (calc_network_input_len nio)
    (calc_network_old_output nio)
    out_contentse
    log
    log1
    consumede
    wire_outputse
    local_outputse;
  let nwritten =
    calc_finish_network_io_observed
      srv
      ch
      frame
      nio
      process_result
      received
      sent
      log
      received1
      sent1
      log1
      out_contentse
      consumede
      wire_outputse
      local_outputse;
  rewrite
    (CalcCP.canonical_server_exactly
      srv
      (Ghost.reveal received1)
      (Ghost.reveal sent1)
      (Ghost.reveal log1))
    as
    (CalcCP.calc_server_protocol_implementation.CPI.pi_invariant
      srv
      (Ghost.reveal received1)
      (Ghost.reveal sent1)
      (Ghost.reveal log1));
  rewrite
    (calc_frame_ready srv () frame (Ghost.reveal log1))
    as
    (calc_protocol_endpoint.PE.pe_frame_ready srv () frame (Ghost.reveal log1));
  rewrite
    (calc_io_ready
      srv
      ch
      frame
      (Ghost.reveal received1)
      (Ghost.reveal sent1)
      (Ghost.reveal log1))
    as
    (calc_protocol_endpoint.PE.pe_io_ready
      srv
      ch
      frame
      (Ghost.reveal received1)
      (Ghost.reveal sent1)
      (Ghost.reveal log1));
  let status = calc_network_driver_status process_result;
  if (nwritten = process_result.CPI.process_produced_len) {
    match status {
      CalcDriverNetworkStep -> {
        ({
          calc_driver_status = CalcDriverNetworkStep;
        })
      }
      CalcDriverFailed -> {
        ({
          calc_driver_status = CalcDriverFailed;
        })
      }
    }
  } else {
    ({
      calc_driver_status = CalcDriverFailed;
    })
  }
}

fn calc_drive_steps_while
  (srv:CalcCP.canonical_server)
  (frame:CalcCP.calc_network_frame)
  (ch:TCP.channel)
  (fuel:SZ.t)
  (received:Ghost.erased TCP.bytes)
  (sent:Ghost.erased TCP.bytes)
  (log:Ghost.erased calc_log)
requires
  CalcCP.calc_server_protocol_implementation.CPI.pi_invariant
    srv
    (Ghost.reveal received)
    (Ghost.reveal sent)
    (Ghost.reveal log) **
  calc_protocol_endpoint.PE.pe_frame_ready
    srv
    ()
    frame
    (Ghost.reveal log) **
  calc_protocol_endpoint.PE.pe_io_ready
    srv
    ch
    frame
    (Ghost.reveal received)
    (Ghost.reveal sent)
    (Ghost.reveal log)
ensures
  exists* (received1:Ghost.erased TCP.bytes)
          (sent1:Ghost.erased TCP.bytes)
          (log1:Ghost.erased calc_log).
    CalcCP.calc_server_protocol_implementation.CPI.pi_invariant
      srv
      (Ghost.reveal received1)
      (Ghost.reveal sent1)
      (Ghost.reveal log1) **
    calc_protocol_endpoint.PE.pe_frame_ready
      srv
      ()
      frame
      (Ghost.reveal log1) **
    calc_protocol_endpoint.PE.pe_io_ready
      srv
      ch
      frame
      (Ghost.reveal received1)
      (Ghost.reveal sent1)
      (Ghost.reveal log1)
{
  let mut remaining = fuel;
  let mut running = true;
  while (
    let keep = R.read running;
    let rem = R.read remaining;
    keep && not (rem = 0sz)
  )
    invariant live remaining
    invariant live running
    invariant exists* received_loop sent_loop log_loop.
      CalcCP.calc_server_protocol_implementation.CPI.pi_invariant
        srv
        (Ghost.reveal received_loop)
        (Ghost.reveal sent_loop)
        (Ghost.reveal log_loop) **
      calc_protocol_endpoint.PE.pe_frame_ready
        srv
        ()
        frame
        (Ghost.reveal log_loop) **
      calc_protocol_endpoint.PE.pe_io_ready
        srv
        ch
        frame
        (Ghost.reveal received_loop)
        (Ghost.reveal sent_loop)
        (Ghost.reveal log_loop) **
      pure (SZ.v (R.read remaining) <= SZ.v fuel)
  decreases %[(if !running then 1 else 0); SZ.v (!remaining)]
  {
    with rem_live keep_live received_loop sent_loop log_loop.
      assert (
        R.pts_to remaining rem_live **
        R.pts_to running keep_live **
        CalcCP.calc_server_protocol_implementation.CPI.pi_invariant
          srv
          (Ghost.reveal received_loop)
          (Ghost.reveal sent_loop)
          (Ghost.reveal log_loop) **
        calc_protocol_endpoint.PE.pe_frame_ready
          srv
          ()
          frame
          (Ghost.reveal log_loop) **
        calc_protocol_endpoint.PE.pe_io_ready
          srv
          ch
          frame
          (Ghost.reveal received_loop)
          (Ghost.reveal sent_loop)
          (Ghost.reveal log_loop) **
        pure (SZ.v rem_live <= SZ.v fuel));
    let step =
      calc_drive_once_network
        srv
        frame
        ch
        received_loop
        sent_loop
        log_loop;
    with received1 sent1 log1.
      assert (
        CalcCP.calc_server_protocol_implementation.CPI.pi_invariant
          srv
          (Ghost.reveal received1)
          (Ghost.reveal sent1)
          (Ghost.reveal log1) **
        calc_protocol_endpoint.PE.pe_frame_ready
          srv
          ()
          frame
          (Ghost.reveal log1) **
        calc_protocol_endpoint.PE.pe_io_ready
          srv
          ch
          frame
          (Ghost.reveal received1)
          (Ghost.reveal sent1)
          (Ghost.reveal log1));
    match step.calc_driver_status {
      CalcDriverNetworkStep -> {
        let rem_now = R.read remaining;
        assert (pure (not (rem_now = 0sz)));
        assert (pure (0 < SZ.v rem_now));
        let next = SZ.sub rem_now 1sz;
        assert (pure (SZ.v next <= SZ.v fuel));
        remaining := next
      }
      CalcDriverFailed -> {
        running := false
      }
    }
  }
}

fn run_channel_endpoint_impl
  (ch:TCP.channel)
  (fuel:SZ.t)
requires TCP.is_channel ch calc_empty_bytes calc_empty_bytes
ensures emp
{
  let srv = CalcCP.new_canonical_server ();
  let req = Vec.alloc 0uy 5sz;
  let resp = Vec.alloc 0uy 5sz;
  let frame : CalcCP.calc_network_frame = {
    CalcCP.calc_network_req = req;
    CalcCP.calc_network_resp = resp;
  };
  assert (pure (frame.CalcCP.calc_network_req == req));
  assert (pure (frame.CalcCP.calc_network_resp == resp));
  rewrite (Vec.pts_to req (Seq.create 5 0uy)) as
    (Vec.pts_to frame.CalcCP.calc_network_req (Seq.create 5 0uy));
  rewrite (Vec.pts_to resp (Seq.create 5 0uy)) as
    (Vec.pts_to frame.CalcCP.calc_network_resp (Seq.create 5 0uy));
  fold (calc_frame_ready srv () frame initial_log);
  fold (calc_io_ready srv ch frame calc_empty_bytes calc_empty_bytes initial_log);
  rewrite
    (CalcCP.canonical_server_exactly srv calc_empty_bytes calc_empty_bytes initial_log)
    as
    (CalcCP.calc_server_protocol_implementation.CPI.pi_invariant
      srv
      calc_empty_bytes
      calc_empty_bytes
      initial_log);
  rewrite
    (calc_frame_ready srv () frame initial_log)
    as
    (calc_protocol_endpoint.PE.pe_frame_ready srv () frame initial_log);
  rewrite
    (calc_io_ready srv ch frame calc_empty_bytes calc_empty_bytes initial_log)
    as
    (calc_protocol_endpoint.PE.pe_io_ready
      srv
      ch
      frame
      calc_empty_bytes
      calc_empty_bytes
      initial_log);
  calc_drive_steps_while
    srv
    frame
    ch
    fuel
    (Ghost.hide calc_empty_bytes)
    (Ghost.hide calc_empty_bytes)
    (Ghost.hide initial_log);
  with received1 sent1 log1. _;
  rewrite
    (calc_protocol_endpoint.PE.pe_frame_ready srv () frame (Ghost.reveal log1))
    as
    (calc_frame_ready srv () frame (Ghost.reveal log1));
  unfold (calc_frame_ready srv () frame (Ghost.reveal log1));
  rewrite
    (calc_protocol_endpoint.PE.pe_io_ready
      srv
      ch
      frame
      (Ghost.reveal received1)
      (Ghost.reveal sent1)
      (Ghost.reveal log1))
    as
    (calc_io_ready srv ch frame (Ghost.reveal received1) (Ghost.reveal sent1) (Ghost.reveal log1));
  rewrite
    (CalcCP.calc_server_protocol_implementation.CPI.pi_invariant
      srv
      (Ghost.reveal received1)
      (Ghost.reveal sent1)
      (Ghost.reveal log1))
    as
    (CalcCP.canonical_server_exactly
      srv
      (Ghost.reveal received1)
      (Ghost.reveal sent1)
      (Ghost.reveal log1));
  unfold (calc_io_ready srv ch frame (Ghost.reveal received1) (Ghost.reveal sent1) (Ghost.reveal log1));
  with raw_received req_bytes resp_bytes. _;
  TCP.close ch;
  Vec.free frame.CalcCP.calc_network_req;
  Vec.free frame.CalcCP.calc_network_resp;
  free_canonical_server srv #received1 #sent1 #log1
}
