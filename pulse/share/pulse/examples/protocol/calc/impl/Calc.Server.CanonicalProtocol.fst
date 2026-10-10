module Calc.Server.CanonicalProtocol

#lang-pulse

open Pulse.Lib.Pervasives

module CPI = Pulse.Lib.Protocol.Implementation
module ID = FStar.IndefiniteDescription
module L = FStar.List.Tot
module LP = FStar.List.Tot.Properties
module MR = Pulse.Lib.MonotonicGhostRef
module Pre = FStar.Preorder
module RTC = FStar.ReflexiveTransitiveClosure
module Seq = FStar.Seq
module SM = Pulse.Lib.Protocol.StateMachine
module SZ = FStar.SizeT
module TCP = Pulse.Lib.TCP
module WF = Pulse.Lib.Protocol.WireFormat
module WFSM = Pulse.Lib.Protocol.WireFormatStateMachine
module U8 = FStar.UInt8
module Vec = Pulse.Lib.Vec

module CalcParser = Calc.Impl.Parser
module CalcP = Calc.Protocol

open Calc.Log
open Calc.Wire
open Calc.Impl.Types

let calc_server_step_rel
  (log0:calc_log)
  (log1:calc_log)
  : prop =
  exists msg.
    CalcP.calc_frame_network_step_ok
      log0
      msg
      log1
      (CalcP.calc_frame_response_for log0 msg)

let calc_server_state_ahead_preorder
  : Pre.preorder calc_log =
  RTC.closure calc_server_step_rel

let calc_server_transition
  (log0:calc_log)
  (msg:CalcP.calc_frame)
  (log1:calc_log)
  : SM.transition calc_log CalcP.calc_frame CalcP.calc_frame_local_event unit =
  let output = {
    SM.so_wire_outputs = [CalcP.calc_frame_response_for log0 msg];
    SM.so_local_outputs = [];
  } in
  {
    SM.tr_event = SM.WireEvent msg;
    SM.tr_next_state = log1;
    SM.tr_output = output;
  }

let lemma_calc_server_step_rel_state_ahead
  (log0:calc_log)
  (log1:calc_log)
  : Lemma
      (requires calc_server_step_rel log0 log1)
      (ensures
        CPI.state_ahead
          CalcP.calc_frame_wire_format_state_machine
          log0
          log1)
=
  let msg =
    FStar.IndefiniteDescription.indefinite_description_ghost
      CalcP.calc_frame
      (fun msg ->
        CalcP.calc_frame_network_step_ok
          log0
          msg
          log1
          (CalcP.calc_frame_response_for log0 msg)) in
  let tr = calc_server_transition log0 msg log1 in
  assert (SM.trace_reaches
    CalcP.calc_frame_wire_format_state_machine.WFSM.wfsm_state_machine
    log0
    [tr]
    log1);
  assert (exists trace.
    SM.trace_reaches
      CalcP.calc_frame_wire_format_state_machine.WFSM.wfsm_state_machine
      log0
      trace
      log1)

let lemma_calc_server_closure_state_ahead
  (log0:calc_log)
  (log1:calc_log)
  : Lemma
      (requires calc_server_state_ahead_preorder log0 log1)
      (ensures
        CPI.state_ahead
          CalcP.calc_frame_wire_format_state_machine
          log0
          log1)
=
  RTC.induct
    calc_server_step_rel
    (fun x y ->
      CPI.state_ahead
        CalcP.calc_frame_wire_format_state_machine
        x
        y)
    (fun x ->
      SM.lemma_state_evolves_refl
        CalcP.calc_frame_wire_format_state_machine.WFSM.wfsm_state_machine
        x)
    (fun x y ->
      lemma_calc_server_step_rel_state_ahead x y)
    (fun x y z ->
      SM.lemma_state_evolves_trans
        CalcP.calc_frame_wire_format_state_machine.WFSM.wfsm_state_machine
        x
        y
        z)
    log0
    log1
    ()

let lemma_calc_server_step_rel_histories_ahead
  (log0:calc_log)
  (log1:calc_log)
  : Lemma
      (requires calc_server_step_rel log0 log1)
      (ensures
        TCP.bytes_extends log0.input_bytes log1.input_bytes /\
        TCP.bytes_extends log0.output_bytes log1.output_bytes)
=
  let msg =
    FStar.IndefiniteDescription.indefinite_description_ghost
      CalcP.calc_frame
      (fun msg ->
        CalcP.calc_frame_network_step_ok
          log0
          msg
          log1
          (CalcP.calc_frame_response_for log0 msg)) in
  assert (CalcP.calc_frame_network_step_ok
    log0
    msg
    log1
    (CalcP.calc_frame_response_for log0 msg));
  assert (Seq.equal log1.input_bytes (Seq.append log0.input_bytes msg));
  assert (Seq.equal
    log1.output_bytes
    (Seq.append log0.output_bytes (CalcP.calc_frame_response_for log0 msg)));
  CPI.lemma_bytes_extends_append_equal log0.input_bytes log1.input_bytes msg;
  CPI.lemma_bytes_extends_append_equal
    log0.output_bytes
    log1.output_bytes
    (CalcP.calc_frame_response_for log0 msg)

let lemma_calc_server_closure_histories_ahead
  (log0:calc_log)
  (log1:calc_log)
  : Lemma
      (requires calc_server_state_ahead_preorder log0 log1)
      (ensures
        TCP.bytes_extends log0.input_bytes log1.input_bytes /\
        TCP.bytes_extends log0.output_bytes log1.output_bytes)
=
  RTC.induct
    calc_server_step_rel
    (fun x y ->
      TCP.bytes_extends x.input_bytes y.input_bytes /\
      TCP.bytes_extends x.output_bytes y.output_bytes)
    (fun x ->
      CPI.lemma_bytes_extends_refl x.input_bytes;
      CPI.lemma_bytes_extends_refl x.output_bytes)
    (fun x y ->
      lemma_calc_server_step_rel_histories_ahead x y)
    (fun x y z ->
      CPI.lemma_bytes_extends_trans x.input_bytes y.input_bytes z.input_bytes;
      CPI.lemma_bytes_extends_trans x.output_bytes y.output_bytes z.output_bytes)
    log0
    log1
    ()

let lemma_calc_valid_initial ()
  : Lemma
      (ensures
        WFSM.valid_byte_trace
          CalcP.calc_frame_wire_format_state_machine
          Seq.empty
          initial_log
          Seq.empty
          Seq.empty)
=
  assert (SM.trace_reaches
    CalcP.calc_frame_wire_format_state_machine.WFSM.wfsm_state_machine
    initial_log
    []
    initial_log);
  assert (WF.parses_as CalcP.calc_frame_wire_format Seq.empty [] Seq.empty);
  assert (Seq.equal Seq.empty (WF.serialize_all CalcP.calc_frame_wire_format []));
  let trace = [] in
  assert (
    SM.trace_reaches
      CalcP.calc_frame_wire_format_state_machine.WFSM.wfsm_state_machine
      CalcP.calc_frame_wire_format_state_machine.WFSM.wfsm_state_machine.SM.sm_initial_state
      trace
      initial_log /\
    WF.parses_as
      CalcP.calc_frame_wire_format
      Seq.empty
      (WFSM.trace_input_messages trace)
      Seq.empty /\
    Seq.equal
      Seq.empty
      (WF.serialize_all
        CalcP.calc_frame_wire_format
        (SM.trace_wire_outputs trace)));
  assert (exists trace.
    SM.trace_reaches
      CalcP.calc_frame_wire_format_state_machine.WFSM.wfsm_state_machine
      CalcP.calc_frame_wire_format_state_machine.WFSM.wfsm_state_machine.SM.sm_initial_state
      trace
      initial_log /\
    WF.parses_as
      CalcP.calc_frame_wire_format
      Seq.empty
      (WFSM.trace_input_messages trace)
      Seq.empty /\
    Seq.equal
      Seq.empty
      (WF.serialize_all
        CalcP.calc_frame_wire_format
        (SM.trace_wire_outputs trace)))

noeq
type canonical_server = {
  canonical_server_state: server_state;
  canonical_server_progress: MR.mref calc_server_state_ahead_preorder;
}

let canonical_trace_witness
  (received:TCP.bytes)
  (sent:TCP.bytes)
  (log:calc_log)
  (trace:list (SM.transition calc_log CalcP.calc_frame CalcP.calc_frame_local_event unit))
  : prop =
  SM.trace_reaches
    CalcP.calc_frame_wire_format_state_machine.WFSM.wfsm_state_machine
    initial_log
    trace
    log /\
  Seq.equal
    received
    (WF.serialize_all
      CalcP.calc_frame_wire_format
      (WFSM.trace_input_messages trace)) /\
  Seq.equal
    sent
    (WF.serialize_all
      CalcP.calc_frame_wire_format
      (SM.trace_wire_outputs trace)) /\
  Seq.equal received log.input_bytes /\
  Seq.equal sent log.output_bytes

let canonical_trace_ok
  (received:TCP.bytes)
  (sent:TCP.bytes)
  (log:calc_log)
  : prop =
  exists trace. canonical_trace_witness received sent log trace

let lemma_canonical_trace_ok_valid
  (received:TCP.bytes)
  (sent:TCP.bytes)
  (log:calc_log)
  : Lemma
      (requires canonical_trace_ok received sent log)
      (ensures
        WFSM.valid_byte_trace
          CalcP.calc_frame_wire_format_state_machine
          received
          log
          sent
          Seq.empty)
=
  let trace =
    ID.indefinite_description_ghost
      (list (SM.transition calc_log CalcP.calc_frame CalcP.calc_frame_local_event unit))
      (canonical_trace_witness received sent log) in
  assert (canonical_trace_witness received sent log trace);
  WF.lemma_parse_serialize_all_inverse
    CalcP.calc_frame_wire_format
    CalcP.calc_frame_wire_format_stream_laws
    (WFSM.trace_input_messages trace);
  Seq.lemma_eq_elim
    received
    (WF.serialize_all
      CalcP.calc_frame_wire_format
      (WFSM.trace_input_messages trace));
  assert (
    WF.parses_as
      CalcP.calc_frame_wire_format
      received
      (WFSM.trace_input_messages trace)
      Seq.empty);
  assert (exists trace'.
    SM.trace_reaches
      CalcP.calc_frame_wire_format_state_machine.WFSM.wfsm_state_machine
      CalcP.calc_frame_wire_format_state_machine.WFSM.wfsm_state_machine.SM.sm_initial_state
      trace'
      log /\
    WF.parses_as
      CalcP.calc_frame_wire_format
      received
      (WFSM.trace_input_messages trace')
      Seq.empty /\
    Seq.equal
      sent
      (WF.serialize_all
        CalcP.calc_frame_wire_format
        (SM.trace_wire_outputs trace')))

let lemma_canonical_trace_ok_network_step
  (received0:TCP.bytes)
  (sent0:TCP.bytes)
  (log0:calc_log)
  (msg:CalcP.calc_frame)
  (log1:calc_log)
  (actual_output:TCP.bytes)
  : Lemma
      (requires
        canonical_trace_ok received0 sent0 log0 /\
        CalcP.calc_frame_network_step_ok log0 msg log1 actual_output)
      (ensures
        canonical_trace_ok
          (Seq.append received0 msg)
          (Seq.append sent0 actual_output)
          log1)
=
  let trace0 =
    ID.indefinite_description_ghost
      (list (SM.transition calc_log CalcP.calc_frame CalcP.calc_frame_local_event unit))
      (canonical_trace_witness received0 sent0 log0) in
  assert (canonical_trace_witness received0 sent0 log0 trace0);
  let response_msg = CalcP.calc_frame_response_for log0 msg in
  let tr = calc_server_transition log0 msg log1 in
  assert (
    CalcP.calc_frame_step
      log0
      (SM.WireEvent msg)
      log1
      tr.SM.tr_output);
  assert (SM.trace_reaches
    CalcP.calc_frame_wire_format_state_machine.WFSM.wfsm_state_machine
    log0
    [tr]
    log1);
  SM.lemma_trace_reaches_append
    CalcP.calc_frame_wire_format_state_machine.WFSM.wfsm_state_machine
    initial_log
    log0
    log1
    trace0
    [tr];
  CalcP.lemma_calc_trace_input_bytes_append_one trace0 tr;
  CalcP.lemma_calc_trace_wire_bytes_append_one trace0 tr;
  Seq.append_empty_r msg;
  Seq.append_empty_r response_msg;
  assert (Seq.equal
    (WF.serialize_all
      CalcP.calc_frame_wire_format
      (WFSM.trace_input_messages (L.append trace0 [tr])))
    (Seq.append
      (WF.serialize_all
        CalcP.calc_frame_wire_format
        (WFSM.trace_input_messages trace0))
      msg));
  assert (Seq.equal
    (WF.serialize_all
      CalcP.calc_frame_wire_format
      (SM.trace_wire_outputs (L.append trace0 [tr])))
    (Seq.append
      (WF.serialize_all
        CalcP.calc_frame_wire_format
        (SM.trace_wire_outputs trace0))
      response_msg));
  Seq.lemma_eq_elim
    received0
    (WF.serialize_all
      CalcP.calc_frame_wire_format
      (WFSM.trace_input_messages trace0));
  Seq.lemma_eq_elim
    sent0
    (WF.serialize_all
      CalcP.calc_frame_wire_format
      (SM.trace_wire_outputs trace0));
  Seq.lemma_eq_elim response_msg actual_output;
  assert (Seq.equal
    (Seq.append received0 msg)
    (WF.serialize_all
      CalcP.calc_frame_wire_format
      (WFSM.trace_input_messages (L.append trace0 [tr]))));
  assert (Seq.equal
    (Seq.append sent0 actual_output)
    (WF.serialize_all
      CalcP.calc_frame_wire_format
      (SM.trace_wire_outputs (L.append trace0 [tr]))));
  assert (Seq.equal (Seq.append received0 msg) log1.input_bytes);
  assert (Seq.equal (Seq.append sent0 actual_output) log1.output_bytes);
  assert (canonical_trace_witness
    (Seq.append received0 msg)
    (Seq.append sent0 actual_output)
    log1
    (L.append trace0 [tr]));
  assert (exists trace.
    canonical_trace_witness
      (Seq.append received0 msg)
      (Seq.append sent0 actual_output)
      log1
      trace)

noeq
type calc_network_frame = {
  calc_network_req: Vec.vec U8.t;
  calc_network_resp: Vec.vec U8.t;
}

type calc_local_frame = unit

[@inline_let]
let calc_process_result
  (status:CPI.process_status)
  (consumed:SZ.t)
  (produced:SZ.t)
  : CPI.process_result =
  {
    CPI.process_status = status;
    CPI.process_consumed_len = consumed;
    CPI.process_produced_len = produced;
    CPI.process_app_len = 0sz;
  }

[@inline_let]
let calc_step_ok_result : CPI.process_result =
  calc_process_result CPI.StepOk 5sz 5sz

let calc_need_more_input_result : CPI.process_result =
  calc_process_result CPI.NeedMoreInput 0sz 0sz

let calc_parse_failed_result : CPI.process_result =
  calc_process_result CPI.ParseFailed 0sz 0sz

let calc_no_local_outputs : list unit = []

let empty_calc_trace
  : list (SM.transition calc_log CalcP.calc_frame CalcP.calc_frame_local_event unit)
  = []

let default_calc_frame : CalcP.calc_frame =
  CalcP.calc_response_frame Error

let parse_request_if_frame
  (b:TCP.bytes)
  : GTot (option request) =
  if Seq.length b == 5 then
    parse_request b
  else
    None

let calc_frame_or_default
  (b:TCP.bytes)
  : GTot CalcP.calc_frame =
  if Seq.length b == 5 then
    match parse_request b with
    | Some _ -> b
    | None -> default_calc_frame
  else
    default_calc_frame

let lemma_calc_frame_or_default_valid
  (b:TCP.bytes{Seq.length b == 5 /\ parse_request b <> None})
  : Lemma
      (ensures calc_frame_or_default b == b)
=
  match parse_request b with
  | Some _ -> ()

let lemma_parse_request_some_if_valid_tag
  (b:TCP.bytes{Seq.length b == 5 /\ U8.v (Seq.index b 0) < 6})
  : Lemma
      (ensures parse_request b <> None)
=
  ()

let lemma_parse_request_none_if_invalid_tag
  (b:TCP.bytes{Seq.length b == 5 /\ 6 <= U8.v (Seq.index b 0)})
  : Lemma
      (ensures parse_request b == None)
=
  ()

let lemma_network_process_correct_step_ok
  (input:TCP.bytes)
  (input_len:SZ.t)
  (old_out:TCP.bytes)
  (out_bytes:TCP.bytes)
  (out_len:SZ.t)
  (received0:TCP.bytes)
  (sent0:TCP.bytes)
  (log0:calc_log)
  (received1:TCP.bytes)
  (sent1:TCP.bytes)
  (log1:calc_log)
  (consumed:TCP.bytes)
  (wire_outputs:list CalcP.calc_frame)
  (local_outputs:list unit)
  (produced:TCP.bytes)
  : Lemma
      (requires
        CPI.buffers_wf input input_len old_out out_len /\
        Seq.length out_bytes == Seq.length old_out /\
        CPI.consumed_by_parse
          CalcP.calc_frame_wire_format
          (CPI.input_bytes input input_len)
          (calc_frame_or_default input)
          consumed
          Seq.empty /\
        SZ.v calc_step_ok_result.CPI.process_consumed_len == Seq.length consumed /\
        CalcP.calc_frame_wire_format_state_machine.WFSM.wfsm_state_machine.SM.sm_step
          log0
          (SM.WireEvent (calc_frame_or_default input))
          log1
          (CPI.step_output wire_outputs local_outputs) /\
        Seq.equal
          produced
          (WF.serialize_all CalcP.calc_frame_wire_format wire_outputs) /\
        CPI.output_written
          out_bytes
          calc_step_ok_result.CPI.process_produced_len
          produced /\
        Seq.equal received1 (Seq.append received0 consumed) /\
        Seq.equal sent1 (Seq.append sent0 produced))
      (ensures
        CPI.network_process_correct
          CalcP.calc_frame_wire_format_state_machine
          input
          input_len
          old_out
          out_bytes
          out_len
          received0
          sent0
          log0
          calc_step_ok_result
          received1
          sent1
          log1
          consumed
          wire_outputs
          local_outputs)
=
  let msg = calc_frame_or_default input in
  assert (CPI.consumed_by_parse
    CalcP.calc_frame_wire_format
    (CPI.input_bytes input input_len)
    msg
    consumed
    Seq.empty);
  assert (SZ.v calc_step_ok_result.CPI.process_consumed_len == Seq.length consumed);
  assert (CalcP.calc_frame_wire_format_state_machine.WFSM.wfsm_state_machine.SM.sm_step
    log0
    (SM.WireEvent msg)
    log1
    (CPI.step_output wire_outputs local_outputs));
  assert (Seq.equal
    produced
    (WF.serialize_all CalcP.calc_frame_wire_format wire_outputs));
  assert (CPI.output_written
    out_bytes
    calc_step_ok_result.CPI.process_produced_len
    produced);
  assert (Seq.equal received1 (Seq.append received0 consumed));
  assert (Seq.equal sent1 (Seq.append sent0 produced));
  assert_norm (calc_step_ok_result.CPI.process_status == CPI.StepOk);
  assert (calc_step_ok_result.CPI.process_status == CPI.StepOk);
  assert (exists msg' residual produced'.
    CPI.consumed_by_parse
      CalcP.calc_frame_wire_format
      (CPI.input_bytes input input_len)
      msg'
      consumed
      residual /\
    SZ.v calc_step_ok_result.CPI.process_consumed_len == Seq.length consumed /\
    CalcP.calc_frame_wire_format_state_machine.WFSM.wfsm_state_machine.SM.sm_step
      log0
      (SM.WireEvent msg')
      log1
      (CPI.step_output wire_outputs local_outputs) /\
    Seq.equal
      produced'
      (WF.serialize_all CalcP.calc_frame_wire_format wire_outputs) /\
    CPI.output_written
      out_bytes
      calc_step_ok_result.CPI.process_produced_len
      produced' /\
    Seq.equal received1 (Seq.append received0 consumed) /\
    Seq.equal sent1 (Seq.append sent0 produced'));
  assert (5 == Seq.length consumed);
  assert (CPI.output_written out_bytes 5sz produced);
  assert (Seq.equal
    produced
    (WF.serialize_all
      CalcP.calc_frame_wire_format_state_machine.WFSM.wfsm_wire_format
      wire_outputs));
  assert (exists msg' residual produced'.
    CPI.consumed_by_parse
      CalcP.calc_frame_wire_format_state_machine.WFSM.wfsm_wire_format
      (CPI.input_bytes input input_len)
      msg'
      consumed
      residual /\
    5 == Seq.length consumed /\
    CalcP.calc_frame_wire_format_state_machine.WFSM.wfsm_state_machine.SM.sm_step
      log0
      (SM.WireEvent msg')
      log1
      (CPI.step_output wire_outputs local_outputs) /\
    Seq.equal
      produced'
      (WF.serialize_all
        CalcP.calc_frame_wire_format_state_machine.WFSM.wfsm_wire_format
        wire_outputs) /\
    CPI.output_written out_bytes 5sz produced' /\
    Seq.equal received1 (Seq.append received0 consumed) /\
    Seq.equal sent1 (Seq.append sent0 produced'));
  match calc_step_ok_result.CPI.process_status with
  | CPI.StepOk ->
    assert (CPI.network_process_correct
      CalcP.calc_frame_wire_format_state_machine
      input
      input_len
      old_out
      out_bytes
      out_len
      received0
      sent0
      log0
      calc_step_ok_result
      received1
      sent1
      log1
      consumed
      wire_outputs
      local_outputs)
    by (
      FStar.Tactics.norm
        [delta_only
          [`%CPI.network_process_correct;
           `%calc_step_ok_result;
           `%calc_process_result;
           `%Pulse.Lib.Protocol.Implementation.__proj__Mkprocess_result__item__process_status;
           `%Pulse.Lib.Protocol.Implementation.__proj__Mkprocess_result__item__process_consumed_len;
           `%Pulse.Lib.Protocol.Implementation.__proj__Mkprocess_result__item__process_produced_len];
         iota; zeta; primops];
      FStar.Tactics.smt ())
  | _ ->
    assert False

let canonical_server_exactly
  (srv:canonical_server)
  (received:TCP.bytes)
  (sent:TCP.bytes)
  (log:calc_log)
  : slprop =
  server_exactly srv.canonical_server_state log **
  MR.pts_to srv.canonical_server_progress #1.0R log **
  pure (canonical_trace_ok received sent log)

let canonical_server_snapshot
  (srv:canonical_server)
  (received:TCP.bytes)
  (sent:TCP.bytes)
  (log:calc_log)
  : slprop =
  MR.snapshot srv.canonical_server_progress log **
  pure (
    Seq.equal received log.input_bytes /\
    Seq.equal sent log.output_bytes)

[@@pulse_unfold]
let calc_network_frame_pre
  (frame:calc_network_frame)
  (input:array U8.t)
  (input_len:SZ.t)
  (out:array U8.t)
  (out_len:SZ.t)
  (input_contents:TCP.bytes)
  (old_out:TCP.bytes)
  : slprop =
  pure (
    input == Vec.vec_to_array frame.calc_network_req /\
    out == Vec.vec_to_array frame.calc_network_resp /\
    Seq.length input_contents == 5 /\
    Seq.length old_out == 5 /\
    input_len == 5sz /\
    out_len == 5sz)

let calc_network_frame_post
  (_frame:calc_network_frame)
  (result:CPI.process_result)
  (input_contents:TCP.bytes)
  (_input_len:SZ.t)
  (old_out:TCP.bytes)
  (out_contents:TCP.bytes)
  (st0:calc_log)
  (st1:calc_log)
  (consumed:TCP.bytes)
  (wire_outputs:list CalcP.calc_frame)
  (local_outputs:list unit)
  : slprop =
  let msg = calc_frame_or_default input_contents in
  let response_msg = CalcP.calc_frame_response_for st0 msg in
  pure (
    match result.CPI.process_status with
    | CPI.StepOk ->
      result == calc_step_ok_result /\
      parse_request_if_frame input_contents <> None /\
      consumed == input_contents /\
      wire_outputs == [response_msg] /\
      local_outputs == [] /\
      CalcP.calc_frame_network_step_ok st0 msg st1 out_contents
    | CPI.ParseFailed ->
      result == calc_parse_failed_result /\
      parse_request_if_frame input_contents == None /\
      Seq.equal consumed Seq.empty /\
      wire_outputs == [] /\
      local_outputs == [] /\
      st1 == st0 /\
      Seq.equal out_contents old_out
    | _ -> False)

[@@pulse_unfold]
let calc_local_frame_pre
  (_ev:CalcP.calc_frame_local_event)
  (_frame:calc_local_frame)
  (_st0:calc_log)
  (_out:array U8.t)
  (_out_len:SZ.t)
  (_old_out:TCP.bytes)
  : slprop =
  emp

let calc_local_frame_post
  (_ev:CalcP.calc_frame_local_event)
  (_frame:calc_local_frame)
  (result:CPI.process_result)
  (old_out:TCP.bytes)
  (out_contents:TCP.bytes)
  (st0:calc_log)
  (st1:calc_log)
  (wire_outputs:list CalcP.calc_frame)
  (local_outputs:list unit)
  : slprop =
  pure (
    result == calc_process_result CPI.StepOk 0sz 0sz /\
    out_contents == old_out /\
    st1 == st0 /\
    wire_outputs == [] /\
    local_outputs == [])

ghost fn calc_invariant_valid
  (srv:canonical_server)
  (received:erased TCP.bytes)
  (sent:erased TCP.bytes)
  (log:erased calc_log)
requires canonical_server_exactly srv received sent log
ensures
  canonical_server_exactly srv received sent log **
  pure (
    WFSM.valid_byte_trace
      CalcP.calc_frame_wire_format_state_machine
      received
      log
      sent
      Seq.empty)
{
  unfold (canonical_server_exactly srv received sent log);
  lemma_canonical_trace_ok_valid received sent log;
  assert (pure (WFSM.valid_byte_trace
    CalcP.calc_frame_wire_format_state_machine
    received
    log
    sent
    Seq.empty));
  fold (canonical_server_exactly srv received sent log)
}

ghost fn calc_take_snapshot
  (srv:canonical_server)
  (received:erased TCP.bytes)
  (sent:erased TCP.bytes)
  (log:erased calc_log)
requires canonical_server_exactly srv received sent log
ensures
  canonical_server_exactly srv received sent log **
  canonical_server_snapshot srv received sent log
{
  unfold (canonical_server_exactly srv received sent log);
  MR.take_snapshot srv.canonical_server_progress log;
  assert (pure (canonical_trace_ok received sent log));
  assert (pure (Seq.equal received log.input_bytes));
  assert (pure (Seq.equal sent log.output_bytes));
  fold (canonical_server_snapshot srv received sent log);
  fold (canonical_server_exactly srv received sent log)
}

ghost fn calc_recall_snapshot
  (srv:canonical_server)
  (snapshot_received:erased TCP.bytes)
  (snapshot_sent:erased TCP.bytes)
  (snapshot_log:erased calc_log)
  (current_received:erased TCP.bytes)
  (current_sent:erased TCP.bytes)
  (current_log:erased calc_log)
requires
  canonical_server_snapshot srv snapshot_received snapshot_sent snapshot_log **
  canonical_server_exactly srv current_received current_sent current_log
ensures
  canonical_server_snapshot srv snapshot_received snapshot_sent snapshot_log **
  canonical_server_exactly srv current_received current_sent current_log **
  pure (
    CPI.state_ahead
      CalcP.calc_frame_wire_format_state_machine
      snapshot_log
      current_log /\
    CPI.histories_ahead
      snapshot_received
      snapshot_sent
      current_received
      current_sent)
{
  unfold (canonical_server_snapshot srv snapshot_received snapshot_sent snapshot_log);
  unfold (canonical_server_exactly srv current_received current_sent current_log);
  MR.recall_snapshot srv.canonical_server_progress;
  lemma_calc_server_closure_state_ahead snapshot_log current_log;
  lemma_calc_server_closure_histories_ahead snapshot_log current_log;
  assert (pure (canonical_trace_ok current_received current_sent current_log));
  assert (pure (Seq.equal snapshot_received snapshot_log.input_bytes));
  assert (pure (Seq.equal snapshot_sent snapshot_log.output_bytes));
  assert (pure (Seq.equal current_received current_log.input_bytes));
  assert (pure (Seq.equal current_sent current_log.output_bytes));
  assert (pure (CPI.histories_ahead
    snapshot_received
    snapshot_sent
    current_received
    current_sent));
  fold (canonical_server_snapshot srv snapshot_received snapshot_sent snapshot_log);
  fold (canonical_server_exactly srv current_received current_sent current_log)
}

#push-options "--z3rlimit 200"
fn calc_process_network
  (srv:canonical_server)
  (frame:calc_network_frame)
  (input:array U8.t)
  (input_len:SZ.t)
  (out:array U8.t)
  (out_len:SZ.t)
  (received0:erased TCP.bytes)
  (sent0:erased TCP.bytes)
  (log0:erased calc_log)
  (input_contents:erased TCP.bytes)
  (old_out:erased TCP.bytes)
requires
  canonical_server_exactly srv received0 sent0 log0 **
  calc_network_frame_pre frame input input_len out out_len input_contents old_out **
  pts_to input input_contents **
  pts_to out old_out **
  pure (CPI.buffers_wf input_contents input_len old_out out_len)
returns result:CPI.process_result
ensures exists* (received1:Ghost.erased TCP.bytes)
                (sent1:Ghost.erased TCP.bytes)
                (log1:Ghost.erased calc_log)
                (out_contents:TCP.bytes)
                (consumed:TCP.bytes)
                (wire_outputs:list CalcP.calc_frame)
                (local_outputs:list unit).
  canonical_server_exactly srv (Ghost.reveal received1) (Ghost.reveal sent1) (Ghost.reveal log1) **
  calc_network_frame_post
    frame
    result
    input_contents
    input_len
    old_out
    out_contents
    log0
    (Ghost.reveal log1)
    consumed
    wire_outputs
    local_outputs **
  pts_to input input_contents **
  pts_to out out_contents **
  pure (
    CPI.network_process_correct
      CalcP.calc_frame_wire_format_state_machine
      input_contents
      input_len
      old_out
      out_contents
      out_len
      received0
      sent0
      log0
      result
      (Ghost.reveal received1)
      (Ghost.reveal sent1)
      (Ghost.reveal log1)
      consumed
      wire_outputs
      local_outputs)
{
  unfold (canonical_server_exactly srv received0 sent0 log0);
  unfold (calc_network_frame_pre frame input input_len out out_len input_contents old_out);
  rewrite (pts_to input input_contents) as (pts_to (Vec.vec_to_array frame.calc_network_req) input_contents);
  rewrite (pts_to out old_out) as (pts_to (Vec.vec_to_array frame.calc_network_resp) old_out);
  Vec.to_vec_pts_to frame.calc_network_req;
  Vec.to_vec_pts_to frame.calc_network_resp;
  let tag = CalcParser.parse_tag frame.calc_network_req;
  if U8.lt tag 6uy {
    assert (pure (U8.v tag < 6));
    assert (pure (tag == Seq.index input_contents 0));
    assert (pure (U8.v (Seq.index input_contents 0) < 6));
    lemma_parse_request_some_if_valid_tag input_contents;
    assert (pure (parse_request input_contents <> None));
    Calc.Server.process_request srv.canonical_server_state frame.calc_network_req frame.calc_network_resp;
    with resp_bytes1 log1. _;
    Vec.to_array_pts_to frame.calc_network_req;
    Vec.to_array_pts_to frame.calc_network_resp;
    rewrite (pts_to (Vec.vec_to_array frame.calc_network_req) input_contents) as (pts_to input input_contents);
    rewrite (pts_to (Vec.vec_to_array frame.calc_network_resp) resp_bytes1) as (pts_to out resp_bytes1);
    let msge : erased CalcP.calc_frame = Ghost.hide (Ghost.reveal input_contents);
    let response_msge : erased CalcP.calc_frame =
      Ghost.hide (CalcP.calc_frame_response_for log0 (Ghost.reveal msge));
    lemma_canonical_trace_ok_network_step received0 sent0 log0 (Ghost.reveal msge) log1 resp_bytes1;
    assert (pure (CalcP.calc_frame_network_step_ok log0 (Ghost.reveal msge) log1 (Ghost.reveal response_msge)));
    assert (pure (calc_server_step_rel log0 log1));
    RTC.closure_step calc_server_step_rel log0 log1;
    MR.update srv.canonical_server_progress log1;
    let received1e = Ghost.hide (Seq.append received0 input_contents);
    let sent1e = Ghost.hide (Seq.append sent0 resp_bytes1);
    let log1e = Ghost.hide log1;
    fold (canonical_server_exactly
      srv
      (Ghost.reveal received1e)
      (Ghost.reveal sent1e)
      (Ghost.reveal log1e));
    lemma_calc_frame_or_default_valid input_contents;
    fold (calc_network_frame_post
      frame
      calc_step_ok_result
      input_contents
      input_len
      old_out
      resp_bytes1
      log0
      (Ghost.reveal log1e)
      input_contents
      [Ghost.reveal response_msge]
      calc_no_local_outputs);
    CalcP.lemma_slice_full_5 (Ghost.reveal msge);
    assert (pure (Seq.equal (CPI.input_bytes input_contents input_len) (Ghost.reveal msge)));
    Seq.lemma_eq_elim (CPI.input_bytes input_contents input_len) (Ghost.reveal msge);
    CalcP.lemma_calc_parse_serialize_exact (Ghost.reveal msge);
    Seq.append_empty_r input_contents;
    assert (pure (CPI.consumed_by_parse
      CalcP.calc_frame_wire_format
      (CPI.input_bytes input_contents input_len)
      (Ghost.reveal msge)
      input_contents
      Seq.empty));
    Seq.lemma_eq_elim (Ghost.reveal response_msge) resp_bytes1;
    Seq.append_empty_r (Ghost.reveal response_msge);
    assert (pure (Seq.equal
      (Ghost.reveal response_msge)
      (WF.serialize_all CalcP.calc_frame_wire_format [Ghost.reveal response_msge])));
    assert (pure (CPI.output_written resp_bytes1 5sz (Ghost.reveal response_msge)));
    assert (pure (SZ.v calc_step_ok_result.CPI.process_consumed_len == Seq.length input_contents));
    assert (pure (Seq.equal (Ghost.reveal received1e) (Seq.append received0 input_contents)));
    assert (pure (Seq.equal (Ghost.reveal sent1e) (Seq.append sent0 (Ghost.reveal response_msge))));
    assert (pure (CalcP.calc_frame_wire_format_state_machine.WFSM.wfsm_state_machine.SM.sm_step
      log0
      (SM.WireEvent (Ghost.reveal msge))
      (Ghost.reveal log1e)
      (CPI.step_output [Ghost.reveal response_msge] calc_no_local_outputs)));
    assert (pure (calc_step_ok_result.CPI.process_status == CPI.StepOk));
    assert (pure (calc_step_ok_result.CPI.process_consumed_len == 5sz));
    assert (pure (calc_step_ok_result.CPI.process_produced_len == 5sz));
    assert (pure (CPI.buffers_wf input_contents input_len old_out out_len));
    assert (pure (Seq.length resp_bytes1 == Seq.length old_out));
    assert (pure (exists produced.
      CPI.consumed_by_parse
        CalcP.calc_frame_wire_format
        (CPI.input_bytes input_contents input_len)
        (Ghost.reveal msge)
        input_contents
        Seq.empty /\
      SZ.v calc_step_ok_result.CPI.process_consumed_len == Seq.length input_contents /\
      CalcP.calc_frame_wire_format_state_machine.WFSM.wfsm_state_machine.SM.sm_step
        log0
        (SM.WireEvent (Ghost.reveal msge))
        (Ghost.reveal log1e)
        (CPI.step_output [Ghost.reveal response_msge] calc_no_local_outputs) /\
      Seq.equal
        produced
        (WF.serialize_all CalcP.calc_frame_wire_format [Ghost.reveal response_msge]) /\
      CPI.output_written resp_bytes1 calc_step_ok_result.CPI.process_produced_len produced /\
      Seq.equal (Ghost.reveal received1e) (Seq.append received0 input_contents) /\
      Seq.equal (Ghost.reveal sent1e) (Seq.append sent0 produced)));
    lemma_network_process_correct_step_ok
      input_contents
      input_len
      old_out
      resp_bytes1
      out_len
      received0
      sent0
      log0
      (Ghost.reveal received1e)
      (Ghost.reveal sent1e)
      (Ghost.reveal log1e)
      input_contents
      [Ghost.reveal response_msge]
      calc_no_local_outputs
      (Ghost.reveal response_msge);
    assert (pure (CPI.network_process_correct
      CalcP.calc_frame_wire_format_state_machine
      input_contents
      input_len
      old_out
      resp_bytes1
      out_len
      received0
      sent0
      log0
      calc_step_ok_result
      (Ghost.reveal received1e)
      (Ghost.reveal sent1e)
      (Ghost.reveal log1e)
      input_contents
      [Ghost.reveal response_msge]
      calc_no_local_outputs));
    calc_process_result CPI.StepOk 5sz 5sz
  } else {
    assert (pure (6 <= U8.v tag));
    assert (pure (tag == Seq.index input_contents 0));
    assert (pure (6 <= U8.v (Seq.index input_contents 0)));
    lemma_parse_request_none_if_invalid_tag input_contents;
    Vec.to_array_pts_to frame.calc_network_req;
    Vec.to_array_pts_to frame.calc_network_resp;
    rewrite (pts_to (Vec.vec_to_array frame.calc_network_req) input_contents) as (pts_to input input_contents);
    rewrite (pts_to (Vec.vec_to_array frame.calc_network_resp) old_out) as (pts_to out old_out);
    fold (canonical_server_exactly srv received0 sent0 log0);
    fold (calc_network_frame_post
      frame
      calc_parse_failed_result
      input_contents
      input_len
      old_out
      old_out
      log0
      log0
      Seq.empty
      []
      []);
    CalcP.lemma_slice_full_5 input_contents;
    assert (pure (Seq.equal (CPI.input_bytes input_contents input_len) input_contents));
    Seq.lemma_eq_elim (CPI.input_bytes input_contents input_len) input_contents;
    assert (pure (CalcP.calc_frame_wire_format.WF.wf_parse input_contents == None));
    assert (pure (CPI.buffers_wf input_contents input_len old_out out_len));
    assert (pure (Seq.length old_out == Seq.length old_out));
    assert (pure (CPI.same_abstract_state received0 sent0 received0 sent0 log0 log0));
    assert (pure (CPI.network_process_correct
      CalcP.calc_frame_wire_format_state_machine
      input_contents
      input_len
      old_out
      old_out
      out_len
      received0
      sent0
      log0
      calc_parse_failed_result
      received0
      sent0
      log0
      Seq.empty
      []
      []));
    calc_process_result CPI.ParseFailed 0sz 0sz
  }
}

#pop-options
fn calc_process_local
  (srv:canonical_server)
  (ev:CalcP.calc_frame_local_event)
  (frame:calc_local_frame)
  (out:array U8.t)
  (out_len:SZ.t)
  (received0:erased TCP.bytes)
  (sent0:erased TCP.bytes)
  (log0:erased calc_log)
  (old_out:erased TCP.bytes)
requires
  canonical_server_exactly srv received0 sent0 log0 **
  calc_local_frame_pre ev frame log0 out out_len old_out **
  pts_to out old_out **
  pure (
    SZ.v out_len == Seq.length old_out /\
    ~ (CPI.no_internal_events #CalcP.calc_frame_local_event ev))
returns result:CPI.process_result
ensures exists* (received1:Ghost.erased TCP.bytes)
                (sent1:Ghost.erased TCP.bytes)
                (log1:Ghost.erased calc_log)
                (out_contents:TCP.bytes)
                (wire_outputs:list CalcP.calc_frame)
                (local_outputs:list unit).
  canonical_server_exactly srv (Ghost.reveal received1) (Ghost.reveal sent1) (Ghost.reveal log1) **
  calc_local_frame_post
    ev
    frame
    result
    old_out
    out_contents
    log0
    (Ghost.reveal log1)
    wire_outputs
    local_outputs **
  pts_to out out_contents **
  pure (
    CPI.local_process_correct
      CalcP.calc_frame_wire_format_state_machine
      ev
      old_out
      out_contents
      out_len
      received0
      sent0
      log0
      result
      (Ghost.reveal received1)
      (Ghost.reveal sent1)
      (Ghost.reveal log1)
      wire_outputs
      local_outputs)
{
  unfold (canonical_server_exactly srv received0 sent0 log0);
  unfold (calc_local_frame_pre ev frame log0 out out_len old_out);
  fold (canonical_server_exactly srv received0 sent0 log0);
  let local_result = calc_process_result CPI.StepOk 0sz 0sz;
  fold (calc_local_frame_post ev frame local_result old_out old_out log0 log0 [] []);
  assert (pure (CPI.local_process_correct
    CalcP.calc_frame_wire_format_state_machine
    ev
    old_out
    old_out
    out_len
    received0
    sent0
    log0
    local_result
    received0
    sent0
    log0
    []
    []));
  local_result
}

fn new_canonical_server ()
requires emp
returns srv:canonical_server
ensures
  canonical_server_exactly srv Seq.empty Seq.empty initial_log **
  pure (
    Vec.is_full_vec srv.canonical_server_state.stack /\
    Vec.is_full_vec srv.canonical_server_state.size)
{
  let server_state = Calc.Server.new_server ();
  let progress = MR.alloc #_ #calc_server_state_ahead_preorder initial_log;
  let srv = {
    canonical_server_state = server_state;
    canonical_server_progress = progress;
  };
  rewrite (server_exactly server_state initial_log) as
    (server_exactly srv.canonical_server_state initial_log);
  rewrite (MR.pts_to progress #1.0R initial_log) as
    (MR.pts_to srv.canonical_server_progress #1.0R initial_log);
  assert (pure (canonical_trace_witness Seq.empty Seq.empty initial_log empty_calc_trace));
  assert (pure (canonical_trace_ok Seq.empty Seq.empty initial_log));
  fold (canonical_server_exactly srv Seq.empty Seq.empty initial_log);
  assert (pure (Vec.is_full_vec srv.canonical_server_state.stack));
  assert (pure (Vec.is_full_vec srv.canonical_server_state.size));
  srv
}

noextract
let calc_server_protocol_implementation
  : CPI.protocol_implementation
      canonical_server
      calc_log
      CalcP.calc_frame
      CalcP.calc_frame_local_event
      unit
  =
  {
    CPI.pi_system = (fun _ -> CalcP.calc_frame_wire_format_state_machine);
    CPI.pi_internal = CPI.no_internal_events #CalcP.calc_frame_local_event;
    CPI.pi_internal_pending = CPI.nothing_pending #calc_log;
    CPI.pi_invariant = canonical_server_exactly;
    CPI.pi_snapshot = canonical_server_snapshot;
    CPI.pi_network_frame = calc_network_frame;
    CPI.pi_network_frame_pre = calc_network_frame_pre;
    CPI.pi_network_frame_post = calc_network_frame_post;
    CPI.pi_local_frame = calc_local_frame;
    CPI.pi_local_frame_pre = calc_local_frame_pre;
    CPI.pi_local_frame_post = calc_local_frame_post;
    CPI.pi_internal_frame_pre =
      CPI.no_internal_frame_pre #calc_local_frame #calc_log;
    CPI.pi_internal_frame_post =
      CPI.no_internal_frame_post #calc_local_frame #calc_log #CalcP.calc_frame #unit;
    CPI.pi_invariant_valid = calc_invariant_valid;
    CPI.pi_take_snapshot = calc_take_snapshot;
    CPI.pi_recall_snapshot = calc_recall_snapshot;
    CPI.pi_process_network = calc_process_network;
    CPI.pi_process_local = calc_process_local;
    CPI.pi_process_internal =
      CPI.quiescent_process_internal
        #_ #calc_log #CalcP.calc_frame #CalcP.calc_frame_local_event #unit #calc_local_frame
        canonical_server_exactly
        (fun _ -> CalcP.calc_frame_wire_format_state_machine);
  }
