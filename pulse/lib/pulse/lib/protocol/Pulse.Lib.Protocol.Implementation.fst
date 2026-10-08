module Pulse.Lib.Protocol.Implementation

#lang-pulse

open Pulse.Lib.Pervasives

module Seq = FStar.Seq
module SM = Pulse.Lib.Protocol.StateMachine
module SZ = FStar.SizeT
module TCP = Pulse.Lib.TCP
module U8 = FStar.UInt8
module WF = Pulse.Lib.Protocol.WireFormat
module WFSM = Pulse.Lib.Protocol.WireFormatStateMachine

type process_status =
  | StepOk
  | NeedMoreInput
  | ParseFailed
  | DecodeError
  | IllegalTransition
  | OutputBufferTooSmall
  | ConnectionFailed

noeq
type process_result = {
  process_status: process_status;
  process_consumed_len: SZ.t;
  process_produced_len: SZ.t;
  process_app_len: SZ.t;
}

noextract
let bounded_len
  (bytes:TCP.bytes)
  (len:SZ.t)
  : nat =
  if SZ.v len <= Seq.length bytes then SZ.v len else Seq.length bytes

noextract
let input_bytes
  (input:TCP.bytes)
  (input_len:SZ.t)
  : TCP.bytes =
  Seq.slice input 0 (bounded_len input input_len)

noextract
let output_prefix
  (out:TCP.bytes)
  (produced_len:SZ.t)
  : TCP.bytes =
  Seq.slice out 0 (bounded_len out produced_len)

let buffers_wf
  (input:TCP.bytes)
  (input_len:SZ.t)
  (out:TCP.bytes)
  (out_len:SZ.t)
  : prop =
  SZ.v input_len <= Seq.length input /\
  SZ.v out_len == Seq.length out

let consumed_by_parse
  (#wire_message:Type0)
  (fmt:WF.wire_format wire_message)
  (available:TCP.bytes)
  (msg:wire_message)
  (consumed:TCP.bytes)
  (residual:TCP.bytes)
  : prop =
  exists parsed_msg.
    fmt.WF.wf_parse available == Some (parsed_msg, residual) /\
    parsed_msg == msg /\
  Seq.equal available (Seq.append consumed residual)

let output_written
  (out_bytes:TCP.bytes)
  (produced_len:SZ.t)
  (produced:TCP.bytes)
  : prop =
  SZ.v produced_len == Seq.length produced /\
  SZ.v produced_len <= Seq.length out_bytes /\
  Seq.equal (output_prefix out_bytes produced_len) produced

let same_abstract_state
  (#state:Type0)
  (received0 sent0 received1 sent1:TCP.bytes)
  (st0 st1:state)
  : prop =
  Seq.equal received1 received0 /\
  Seq.equal sent1 sent0 /\
  st1 == st0

let no_progress_status (status:process_status) : bool =
  match status with
  | NeedMoreInput
  | ParseFailed -> true
  | _ -> false

let non_step_status (status:process_status) : bool =
  match status with
  | DecodeError
  | IllegalTransition
  | OutputBufferTooSmall
  | ConnectionFailed -> true
  | _ -> false

let step_output
  (#wire_message:Type0)
  (#local_output:Type0)
  (wire_outputs:list wire_message)
  (local_outputs:list local_output)
  : SM.step_output wire_message local_output =
  {
    SM.so_wire_outputs = wire_outputs;
    SM.so_local_outputs = local_outputs;
  }

let state_ahead
  (#state:Type0)
  (#wire_message:Type0)
  (#local_event:Type0)
  (#local_output:Type0)
  (system:WFSM.wire_format_state_machine state wire_message local_event local_output)
  (st0:state)
  (st1:state)
  : prop =
  exists trace.
    SM.trace_reaches system.WFSM.wfsm_state_machine st0 trace st1

let histories_ahead
  (snapshot_received:TCP.bytes)
  (snapshot_sent:TCP.bytes)
  (current_received:TCP.bytes)
  (current_sent:TCP.bytes)
  : prop =
  TCP.bytes_extends snapshot_received current_received /\
  TCP.bytes_extends snapshot_sent current_sent

let lemma_bytes_extends_refl (bytes:TCP.bytes)
  : Lemma (TCP.bytes_extends bytes bytes)
=
  Seq.lemma_len_slice bytes 0 (Seq.length bytes);
  assert (forall (i:nat{i < Seq.length bytes}).
            Seq.index bytes i == Seq.index (Seq.slice bytes 0 (Seq.length bytes)) i);
  Seq.lemma_eq_intro bytes (Seq.slice bytes 0 (Seq.length bytes))

let lemma_bytes_extends_append (old:TCP.bytes) (delta:TCP.bytes)
  : Lemma (TCP.bytes_extends old (Seq.append old delta))
=
  Seq.lemma_len_append old delta;
  Seq.lemma_len_slice (Seq.append old delta) 0 (Seq.length old);
  assert (forall (i:nat{i < Seq.length old}).
            Seq.index old i ==
            Seq.index (Seq.slice (Seq.append old delta) 0 (Seq.length old)) i);
  Seq.lemma_eq_intro old (Seq.slice (Seq.append old delta) 0 (Seq.length old))

let lemma_bytes_extends_append_equal
  (old:TCP.bytes)
  (next:TCP.bytes)
  (delta:TCP.bytes)
  : Lemma
      (requires Seq.equal next (Seq.append old delta))
      (ensures TCP.bytes_extends old next)
=
  lemma_bytes_extends_append old delta;
  Seq.lemma_eq_elim next (Seq.append old delta);
  assert (TCP.bytes_extends old next)

let lemma_bytes_extends_trans
  (old:TCP.bytes)
  (mid:TCP.bytes)
  (next:TCP.bytes)
  : Lemma
      (requires TCP.bytes_extends old mid /\ TCP.bytes_extends mid next)
      (ensures TCP.bytes_extends old next)
=
  Seq.lemma_len_slice next 0 (Seq.length old);
  Seq.lemma_eq_elim old (Seq.slice mid 0 (Seq.length old));
  Seq.lemma_eq_elim mid (Seq.slice next 0 (Seq.length mid));
  assert (forall (i:nat{i < Seq.length old}).
            Seq.index old i == Seq.index (Seq.slice next 0 (Seq.length old)) i);
  Seq.lemma_eq_intro old (Seq.slice next 0 (Seq.length old))

let network_error_refines_state_machine
  (#state:Type0)
  (#wire_message:Type0)
  (#local_event:Type0)
  (#local_output:Type0)
  (system:WFSM.wire_format_state_machine state wire_message local_event local_output)
  (available:TCP.bytes)
  (st0:state)
  (st1:state)
  (consumed:TCP.bytes)
  (wire_outputs:list wire_message)
  (local_outputs:list local_output)
  : prop =
  (exists msg residual.
    consumed_by_parse
      system.WFSM.wfsm_wire_format
      available
      msg
      consumed
      residual /\
    system.WFSM.wfsm_state_machine.SM.sm_step
      st0
      (SM.WireEvent msg)
      st1
      (step_output wire_outputs local_outputs)) \/
  (exists ev.
    Seq.equal consumed Seq.empty /\
    system.WFSM.wfsm_state_machine.SM.sm_step
      st0
      (SM.LocalEvent ev)
      st1
      (step_output wire_outputs local_outputs)) \/
  (Seq.equal consumed Seq.empty /\
   wire_outputs == [] /\
   local_outputs == [] /\
   st1 == st0)

let local_error_refines_state_machine
  (#state:Type0)
  (#wire_message:Type0)
  (#local_event:Type0)
  (#local_output:Type0)
  (system:WFSM.wire_format_state_machine state wire_message local_event local_output)
  (st0:state)
  (st1:state)
  (wire_outputs:list wire_message)
  (local_outputs:list local_output)
  : prop =
  (exists ev.
    system.WFSM.wfsm_state_machine.SM.sm_step
      st0
      (SM.LocalEvent ev)
      st1
      (step_output wire_outputs local_outputs)) \/
  (wire_outputs == [] /\
   local_outputs == [] /\
   st1 == st0)

let lemma_local_error_refines_from_step
  (#state:Type0)
  (#wire_message:Type0)
  (#local_event:Type0)
  (#local_output:Type0)
  (system:WFSM.wire_format_state_machine state wire_message local_event local_output)
  (st0:state)
  (ev:local_event)
  (st1:state)
  (wire_outputs:list wire_message)
  (local_outputs:list local_output)
  : Lemma
      (requires
        system.WFSM.wfsm_state_machine.SM.sm_step
          st0
          (SM.LocalEvent ev)
          st1
          (step_output wire_outputs local_outputs))
      (ensures
        local_error_refines_state_machine
          system
          st0
          st1
          wire_outputs
          local_outputs)
=
  assert (exists ev'.
    system.WFSM.wfsm_state_machine.SM.sm_step
      st0
      (SM.LocalEvent ev')
      st1
      (step_output wire_outputs local_outputs));
  assert (local_error_refines_state_machine
    system
    st0
    st1
    wire_outputs
    local_outputs)

let network_process_correct
  (#state:Type0)
  (#wire_message:Type0)
  (#local_event:Type0)
  (#local_output:Type0)
  (system:WFSM.wire_format_state_machine state wire_message local_event local_output)
  (input:TCP.bytes)
  (input_len:SZ.t)
  (old_out out_bytes:TCP.bytes)
  (out_len:SZ.t)
  (received0 sent0:TCP.bytes)
  (st0:state)
  (result:process_result)
  (received1 sent1:TCP.bytes)
  (st1:state)
  (consumed:TCP.bytes)
  (wire_outputs:list wire_message)
  (local_outputs:list local_output)
  : prop =
  buffers_wf input input_len old_out out_len /\
  Seq.length out_bytes == Seq.length old_out /\
  (match result.process_status with
  | StepOk ->
    exists msg residual produced.
      consumed_by_parse
        system.WFSM.wfsm_wire_format
        (input_bytes input input_len)
        msg
        consumed
        residual /\
      SZ.v result.process_consumed_len == Seq.length consumed /\
      system.WFSM.wfsm_state_machine.SM.sm_step
        st0
        (SM.WireEvent msg)
        st1
        (step_output wire_outputs local_outputs) /\
      Seq.equal
        produced
        (WF.serialize_all system.WFSM.wfsm_wire_format wire_outputs) /\
      output_written out_bytes result.process_produced_len produced /\
      Seq.equal received1 (Seq.append received0 consumed) /\
      Seq.equal sent1 (Seq.append sent0 produced)
  | NeedMoreInput ->
    system.WFSM.wfsm_wire_format.WF.wf_parse (input_bytes input input_len) == None /\
    Seq.equal consumed Seq.empty /\
    wire_outputs == [] /\
    local_outputs == [] /\
    result.process_consumed_len == 0sz /\
    result.process_produced_len == 0sz /\
    same_abstract_state received0 sent0 received1 sent1 st0 st1 /\
    Seq.equal out_bytes old_out
  | ParseFailed ->
    system.WFSM.wfsm_wire_format.WF.wf_parse (input_bytes input input_len) == None /\
    Seq.equal consumed Seq.empty /\
    wire_outputs == [] /\
    local_outputs == [] /\
    result.process_consumed_len == 0sz /\
    result.process_produced_len == 0sz /\
    same_abstract_state received0 sent0 received1 sent1 st0 st1 /\
    Seq.equal out_bytes old_out
  | OutputBufferTooSmall ->
    exists msg parsed_consumed residual produced st_candidate.
      consumed_by_parse
        system.WFSM.wfsm_wire_format
        (input_bytes input input_len)
        msg
        parsed_consumed
        residual /\
      system.WFSM.wfsm_state_machine.SM.sm_step
        st0
        (SM.WireEvent msg)
        st_candidate
        (step_output wire_outputs local_outputs) /\
      Seq.equal
        produced
        (WF.serialize_all system.WFSM.wfsm_wire_format wire_outputs) /\
      SZ.v out_len < Seq.length produced /\
      Seq.equal consumed Seq.empty /\
      result.process_consumed_len == 0sz /\
      result.process_produced_len == 0sz /\
      same_abstract_state received0 sent0 received1 sent1 st0 st1 /\
      Seq.equal out_bytes old_out
  | DecodeError
  | IllegalTransition
  | ConnectionFailed ->
    exists produced.
      SZ.v result.process_consumed_len == Seq.length consumed /\
      network_error_refines_state_machine
        system
        (input_bytes input input_len)
        st0
        st1
        consumed
        wire_outputs
        local_outputs /\
      Seq.equal
        produced
        (WF.serialize_all system.WFSM.wfsm_wire_format wire_outputs) /\
      output_written out_bytes result.process_produced_len produced /\
      Seq.equal received1 (Seq.append received0 consumed) /\
      Seq.equal sent1 (Seq.append sent0 produced))

let local_process_correct
  (#state:Type0)
  (#wire_message:Type0)
  (#local_event:Type0)
  (#local_output:Type0)
  (system:WFSM.wire_format_state_machine state wire_message local_event local_output)
  (ev:local_event)
  (old_out out_bytes:TCP.bytes)
  (out_len:SZ.t)
  (received0 sent0:TCP.bytes)
  (st0:state)
  (result:process_result)
  (received1 sent1:TCP.bytes)
  (st1:state)
  (wire_outputs:list wire_message)
  (local_outputs:list local_output)
  : prop =
  SZ.v out_len == Seq.length old_out /\
  Seq.length out_bytes == Seq.length old_out /\
  result.process_consumed_len == 0sz /\
  (match result.process_status with
  | StepOk ->
    exists produced.
      system.WFSM.wfsm_state_machine.SM.sm_step
        st0
        (SM.LocalEvent ev)
        st1
        (step_output wire_outputs local_outputs) /\
      Seq.equal
        produced
        (WF.serialize_all system.WFSM.wfsm_wire_format wire_outputs) /\
      output_written out_bytes result.process_produced_len produced /\
      Seq.equal received1 received0 /\
      Seq.equal sent1 (Seq.append sent0 produced)
  | NeedMoreInput ->
    False
  | ParseFailed ->
    False
  | OutputBufferTooSmall ->
    exists produced st_candidate.
      system.WFSM.wfsm_state_machine.SM.sm_step
        st0
        (SM.LocalEvent ev)
        st_candidate
        (step_output wire_outputs local_outputs) /\
      Seq.equal
        produced
        (WF.serialize_all system.WFSM.wfsm_wire_format wire_outputs) /\
      SZ.v out_len < Seq.length produced /\
      result.process_produced_len == 0sz /\
      same_abstract_state received0 sent0 received1 sent1 st0 st1 /\
      Seq.equal out_bytes old_out
  | DecodeError
  | IllegalTransition
  | ConnectionFailed ->
    exists produced.
      local_error_refines_state_machine
        system
        st0
        st1
        wire_outputs
        local_outputs /\
      Seq.equal
        produced
        (WF.serialize_all system.WFSM.wfsm_wire_format wire_outputs) /\
      output_written out_bytes result.process_produced_len produced /\
      Seq.equal received1 received0 /\
      Seq.equal sent1 (Seq.append sent0 produced))

let lemma_local_process_error_refines_step
  (#state:Type0)
  (#wire_message:Type0)
  (#local_event:Type0)
  (#local_output:Type0)
  (system:WFSM.wire_format_state_machine state wire_message local_event local_output)
  (ev:local_event)
  (step_ev:local_event)
  (old_out out_bytes:TCP.bytes)
  (out_len:SZ.t)
  (received0 sent0:TCP.bytes)
  (st0:state)
  (result:process_result)
  (received1 sent1:TCP.bytes)
  (st1:state)
  (wire_outputs:list wire_message)
  (local_outputs:list local_output)
  (produced:TCP.bytes)
  : Lemma
      (requires
        SZ.v out_len == Seq.length old_out /\
        Seq.length out_bytes == Seq.length old_out /\
        result.process_consumed_len == 0sz /\
        (result.process_status == DecodeError \/
         result.process_status == IllegalTransition \/
         result.process_status == ConnectionFailed) /\
        system.WFSM.wfsm_state_machine.SM.sm_step
          st0
          (SM.LocalEvent step_ev)
          st1
          (step_output wire_outputs local_outputs) /\
        Seq.equal
          produced
          (WF.serialize_all system.WFSM.wfsm_wire_format wire_outputs) /\
        output_written out_bytes result.process_produced_len produced /\
        Seq.equal received1 received0 /\
        Seq.equal sent1 (Seq.append sent0 produced))
      (ensures
        local_process_correct
          system
          ev
          old_out
          out_bytes
          out_len
          received0
          sent0
          st0
          result
          received1
          sent1
          st1
          wire_outputs
          local_outputs)
=
  lemma_local_error_refines_from_step
    system
    st0
    step_ev
    st1
    wire_outputs
    local_outputs;
  assert (local_error_refines_state_machine
    system
    st0
    st1
    wire_outputs
    local_outputs);
  assert (exists produced'.
    local_error_refines_state_machine
      system
      st0
      st1
      wire_outputs
      local_outputs /\
    Seq.equal
      produced'
      (WF.serialize_all system.WFSM.wfsm_wire_format wire_outputs) /\
    output_written out_bytes result.process_produced_len produced' /\
    Seq.equal received1 received0 /\
    Seq.equal sent1 (Seq.append sent0 produced'));
  match result.process_status with
  | DecodeError
  | IllegalTransition
  | ConnectionFailed ->
    assert (local_process_correct
      system
      ev
      old_out
      out_bytes
      out_len
      received0
      sent0
      st0
      result
      received1
      sent1
      st1
      wire_outputs
      local_outputs)
  | _ ->
    assert False

let lemma_network_process_ok_refines_transition
  (#state:Type0)
  (#wire_message:Type0)
  (#local_event:Type0)
  (#local_output:Type0)
  (system:WFSM.wire_format_state_machine state wire_message local_event local_output)
  (input:TCP.bytes)
  (input_len:SZ.t)
  (old_out out_bytes:TCP.bytes)
  (out_len:SZ.t)
  (received0 sent0:TCP.bytes)
  (st0:state)
  (result:process_result)
  (received1 sent1:TCP.bytes)
  (st1:state)
  (consumed:TCP.bytes)
  (wire_outputs:list wire_message)
  (local_outputs:list local_output)
  : Lemma
      (requires
        network_process_correct
          system
          input
          input_len
          old_out
          out_bytes
          out_len
          received0
          sent0
          st0
          result
          received1
          sent1
          st1
          consumed
          wire_outputs
          local_outputs /\
        result.process_status == StepOk)
      (ensures
        exists msg residual produced.
          consumed_by_parse
            system.WFSM.wfsm_wire_format
            (input_bytes input input_len)
            msg
            consumed
            residual /\
          SZ.v result.process_consumed_len == Seq.length consumed /\
          system.WFSM.wfsm_state_machine.SM.sm_step
            st0
            (SM.WireEvent msg)
            st1
            (step_output wire_outputs local_outputs) /\
          Seq.equal
            produced
            (WF.serialize_all system.WFSM.wfsm_wire_format wire_outputs) /\
          output_written out_bytes result.process_produced_len produced /\
          Seq.equal received1 (Seq.append received0 consumed) /\
          Seq.equal sent1 (Seq.append sent0 produced))
=
  ()

let lemma_local_process_ok_refines_transition
  (#state:Type0)
  (#wire_message:Type0)
  (#local_event:Type0)
  (#local_output:Type0)
  (system:WFSM.wire_format_state_machine state wire_message local_event local_output)
  (ev:local_event)
  (old_out out_bytes:TCP.bytes)
  (out_len:SZ.t)
  (received0 sent0:TCP.bytes)
  (st0:state)
  (result:process_result)
  (received1 sent1:TCP.bytes)
  (st1:state)
  (wire_outputs:list wire_message)
  (local_outputs:list local_output)
  : Lemma
      (requires
        local_process_correct
          system
          ev
          old_out
          out_bytes
          out_len
          received0
          sent0
          st0
          result
          received1
          sent1
          st1
          wire_outputs
          local_outputs /\
        result.process_status == StepOk)
      (ensures
        exists produced.
          system.WFSM.wfsm_state_machine.SM.sm_step
            st0
            (SM.LocalEvent ev)
            st1
            (step_output wire_outputs local_outputs) /\
          Seq.equal
            produced
            (WF.serialize_all system.WFSM.wfsm_wire_format wire_outputs) /\
          output_written out_bytes result.process_produced_len produced /\
          Seq.equal received1 received0 /\
          Seq.equal sent1 (Seq.append sent0 produced))
=
  ()

let lemma_output_prefix_empty
  (out_bytes:TCP.bytes)
  : Lemma
      (ensures Seq.equal (output_prefix out_bytes 0sz) Seq.empty)
=
  Seq.lemma_len_slice out_bytes 0 0;
  Seq.lemma_eq_intro (output_prefix out_bytes 0sz) Seq.empty

let lemma_network_process_sent_output_prefix
  (#state:Type0)
  (#wire_message:Type0)
  (#local_event:Type0)
  (#local_output:Type0)
  (system:WFSM.wire_format_state_machine state wire_message local_event local_output)
  (input:TCP.bytes)
  (input_len:SZ.t)
  (old_out out_bytes:TCP.bytes)
  (out_len:SZ.t)
  (received0 sent0:TCP.bytes)
  (st0:state)
  (result:process_result)
  (received1 sent1:TCP.bytes)
  (st1:state)
  (consumed:TCP.bytes)
  (wire_outputs:list wire_message)
  (local_outputs:list local_output)
  : Lemma
      (requires
        network_process_correct
          system
          input
          input_len
          old_out
          out_bytes
          out_len
          received0
          sent0
          st0
          result
          received1
          sent1
          st1
          consumed
          wire_outputs
          local_outputs)
      (ensures
        SZ.v result.process_produced_len <= Seq.length out_bytes /\
        Seq.equal
          sent1
          (Seq.append sent0 (output_prefix out_bytes result.process_produced_len)))
=
  match result.process_status with
  | StepOk ->
    let produced =
      FStar.IndefiniteDescription.indefinite_description_ghost
        TCP.bytes
        (fun produced ->
          exists msg residual.
            consumed_by_parse
              system.WFSM.wfsm_wire_format
              (input_bytes input input_len)
              msg
              consumed
              residual /\
            SZ.v result.process_consumed_len == Seq.length consumed /\
            system.WFSM.wfsm_state_machine.SM.sm_step
              st0
              (SM.WireEvent msg)
              st1
              (step_output wire_outputs local_outputs) /\
            Seq.equal
              produced
              (WF.serialize_all system.WFSM.wfsm_wire_format wire_outputs) /\
            output_written out_bytes result.process_produced_len produced /\
            Seq.equal received1 (Seq.append received0 consumed) /\
            Seq.equal sent1 (Seq.append sent0 produced)) in
    assert (output_written out_bytes result.process_produced_len (Ghost.reveal produced));
    Seq.lemma_eq_elim (output_prefix out_bytes result.process_produced_len) (Ghost.reveal produced);
    assert (Seq.equal sent1 (Seq.append sent0 (output_prefix out_bytes result.process_produced_len)))
  | NeedMoreInput
  | ParseFailed ->
    lemma_output_prefix_empty out_bytes;
    Seq.append_empty_r sent0;
    assert (Seq.equal sent1 sent0);
    assert (Seq.equal sent1 (Seq.append sent0 (output_prefix out_bytes result.process_produced_len)))
  | OutputBufferTooSmall ->
    lemma_output_prefix_empty out_bytes;
    Seq.append_empty_r sent0;
    assert (Seq.equal sent1 sent0);
    assert (Seq.equal sent1 (Seq.append sent0 (output_prefix out_bytes result.process_produced_len)))
  | DecodeError
  | IllegalTransition
  | ConnectionFailed ->
    let produced =
      FStar.IndefiniteDescription.indefinite_description_ghost
        TCP.bytes
        (fun produced ->
          SZ.v result.process_consumed_len == Seq.length consumed /\
          network_error_refines_state_machine
            system
            (input_bytes input input_len)
            st0
            st1
            consumed
            wire_outputs
            local_outputs /\
          Seq.equal
            produced
            (WF.serialize_all system.WFSM.wfsm_wire_format wire_outputs) /\
          output_written out_bytes result.process_produced_len produced /\
          Seq.equal received1 (Seq.append received0 consumed) /\
          Seq.equal sent1 (Seq.append sent0 produced)) in
    assert (output_written out_bytes result.process_produced_len (Ghost.reveal produced));
    Seq.lemma_eq_elim (output_prefix out_bytes result.process_produced_len) (Ghost.reveal produced);
    assert (Seq.equal sent1 (Seq.append sent0 (output_prefix out_bytes result.process_produced_len)))

let lemma_local_process_sent_output_prefix
  (#state:Type0)
  (#wire_message:Type0)
  (#local_event:Type0)
  (#local_output:Type0)
  (system:WFSM.wire_format_state_machine state wire_message local_event local_output)
  (ev:local_event)
  (old_out out_bytes:TCP.bytes)
  (out_len:SZ.t)
  (received0 sent0:TCP.bytes)
  (st0:state)
  (result:process_result)
  (received1 sent1:TCP.bytes)
  (st1:state)
  (wire_outputs:list wire_message)
  (local_outputs:list local_output)
  : Lemma
      (requires
        local_process_correct
          system
          ev
          old_out
          out_bytes
          out_len
          received0
          sent0
          st0
          result
          received1
          sent1
          st1
          wire_outputs
          local_outputs)
      (ensures
        SZ.v result.process_produced_len <= Seq.length out_bytes /\
        Seq.equal
          sent1
          (Seq.append sent0 (output_prefix out_bytes result.process_produced_len)))
=
  match result.process_status with
  | StepOk ->
    let produced =
      FStar.IndefiniteDescription.indefinite_description_ghost
        TCP.bytes
        (fun produced ->
          system.WFSM.wfsm_state_machine.SM.sm_step
            st0
            (SM.LocalEvent ev)
            st1
            (step_output wire_outputs local_outputs) /\
          Seq.equal
            produced
            (WF.serialize_all system.WFSM.wfsm_wire_format wire_outputs) /\
          output_written out_bytes result.process_produced_len produced /\
          Seq.equal received1 received0 /\
          Seq.equal sent1 (Seq.append sent0 produced)) in
    assert (output_written out_bytes result.process_produced_len (Ghost.reveal produced));
    Seq.lemma_eq_elim (output_prefix out_bytes result.process_produced_len) (Ghost.reveal produced);
    assert (Seq.equal sent1 (Seq.append sent0 (output_prefix out_bytes result.process_produced_len)))
  | NeedMoreInput
  | ParseFailed ->
    assert False
  | OutputBufferTooSmall ->
    lemma_output_prefix_empty out_bytes;
    Seq.append_empty_r sent0;
    assert (Seq.equal sent1 sent0);
    assert (Seq.equal sent1 (Seq.append sent0 (output_prefix out_bytes result.process_produced_len)))
  | DecodeError
  | IllegalTransition
  | ConnectionFailed ->
    let produced =
      FStar.IndefiniteDescription.indefinite_description_ghost
        TCP.bytes
        (fun produced ->
          local_error_refines_state_machine
            system
            st0
            st1
            wire_outputs
            local_outputs /\
          Seq.equal
            produced
            (WF.serialize_all system.WFSM.wfsm_wire_format wire_outputs) /\
          output_written out_bytes result.process_produced_len produced /\
          Seq.equal received1 received0 /\
          Seq.equal sent1 (Seq.append sent0 produced)) in
    assert (output_written out_bytes result.process_produced_len (Ghost.reveal produced));
    Seq.lemma_eq_elim (output_prefix out_bytes result.process_produced_len) (Ghost.reveal produced);
    assert (Seq.equal sent1 (Seq.append sent0 (output_prefix out_bytes result.process_produced_len)))

(* ==================================================================== *)
(* Internal events                                                       *)
(*                                                                       *)
(* An INTERNAL event is a local event that the implementation selects     *)
(* from its own state rather than receiving from its caller.  The         *)
(* motivating case is a TLS record whose plaintext coalesces several      *)
(* handshake messages: the record itself is one wire event, and each      *)
(* further message it carries is an internal transition driven by         *)
(* plaintext the implementation has already buffered.                     *)
(*                                                                       *)
(* Internal events are NOT a new event class in [Pulse.Lib.Protocol.StateMachine].    *)
(* They are a distinguished SUBSET of the existing local events, singled  *)
(* out by [pi_internal].  This is deliberate.  The generic layers already *)
(* implement exactly this notion: [Pulse.Lib.Protocol.SystemProduct.product_step]     *)
(* gates the local move families as quiet-to-quiet, and                   *)
(* [Pulse.Lib.Protocol.MachineProduct.mp_client_local] is already documented as "a    *)
(* local event that emits nothing on the wire".  Introducing a fifth type *)
(* parameter or a third [event] constructor would duplicate machinery     *)
(* that is already present and correct.                                   *)
(*                                                                       *)
(* An internal event MAY emit wire output.  Nothing here forbids it, and  *)
(* [mp_client_send] already models a local event that puts payload in     *)
(* flight, so the distinction in the product is by wire output, not by    *)
(* who chose the event.  TLS does not need it today, but a protocol that  *)
(* answers a buffered request without a fresh network read does.          *)
(* ==================================================================== *)

(* The outcome of asking an implementation to make internal progress. *)
type internal_status =
  (* An internal transition was taken.  The abstract state advanced. *)
  | InternalProgress
  (* Nothing is pending.  It is safe to read the network. *)
  | InternalQuiescent
  (* Something IS pending, but no internal transition is currently
     enabled: the implementation is waiting on a local action from its
     caller.  Reading the network here would interleave a fresh record
     into one that has not been fully consumed, so a scheduler must
     treat this case as distinct from quiescence.

     TLS reaches this state on every full handshake: after the
     [Certificate] message of a coalesced server flight the client sits
     at [HsCertificateValidated]'s predecessor with unconsumed plaintext
     and no enabled step, because only the local event
     [LocalValidateCertificate] can advance it. *)
  | InternalBlocked
  (* The pending work is unprocessable.  The abstract state moved to a
     failed state, or did not move at all. *)
  | InternalFailed

noeq
type internal_result = {
  internal_status: internal_status;
  internal_process: process_result;
}

(* Some internal transition is enabled in [st0]. *)
let internal_step_enabled
  (#state:Type0)
  (#wire_message:Type0)
  (#local_event:Type0)
  (#local_output:Type0)
  (system:WFSM.wire_format_state_machine state wire_message local_event local_output)
  (is_internal:local_event -> bool)
  (st0:state)
  : prop =
  exists (ev:local_event)
         (st1:state)
         (output:SM.step_output wire_message local_output).
    is_internal ev /\
    system.WFSM.wfsm_state_machine.SM.sm_step st0 (SM.LocalEvent ev) st1 output

let no_internal_step_enabled
  (#state:Type0)
  (#wire_message:Type0)
  (#local_event:Type0)
  (#local_output:Type0)
  (system:WFSM.wire_format_state_machine state wire_message local_event local_output)
  (is_internal:local_event -> bool)
  (st0:state)
  : prop =
  ~ (internal_step_enabled system is_internal st0)

(* The no-op shape shared by [InternalQuiescent] and [InternalBlocked]:
   nothing was consumed, nothing was produced, and neither the abstract
   state nor the output buffer moved. *)
let internal_no_progress
  (#state:Type0)
  (old_out out_bytes:TCP.bytes)
  (received0 sent0:TCP.bytes)
  (st0:state)
  (result:internal_result)
  (received1 sent1:TCP.bytes)
  (st1:state)
  (wire_outputs:list 'wm)
  (local_outputs:list 'lo)
  : prop =
  result.internal_process.process_status == StepOk /\
  result.internal_process.process_consumed_len == 0sz /\
  result.internal_process.process_produced_len == 0sz /\
  result.internal_process.process_app_len == 0sz /\
  wire_outputs == [] /\
  local_outputs == [] /\
  same_abstract_state received0 sent0 received1 sent1 st0 st1 /\
  Seq.equal out_bytes old_out

(* The correctness contract for [pi_process_internal].
                                                                          
   [InternalProgress] and [InternalFailed] are stated by REUSING
   [local_process_correct] at an existentially quantified internal event.
   That is the whole content of decision S1: an internal step IS a local
   step whose event the implementation chose for itself, so it inherits
   the refinement argument that local events already have rather than
   needing a parallel one. *)
let internal_process_correct
  (#state:Type0)
  (#wire_message:Type0)
  (#local_event:Type0)
  (#local_output:Type0)
  (system:WFSM.wire_format_state_machine state wire_message local_event local_output)
  (is_internal:local_event -> bool)
  (pending:state -> prop)
  (old_out out_bytes:TCP.bytes)
  (out_len:SZ.t)
  (received0 sent0:TCP.bytes)
  (st0:state)
  (result:internal_result)
  (received1 sent1:TCP.bytes)
  (st1:state)
  (wire_outputs:list wire_message)
  (local_outputs:list local_output)
  : prop =
  SZ.v out_len == Seq.length old_out /\
  Seq.length out_bytes == Seq.length old_out /\
  result.internal_process.process_consumed_len == 0sz /\
  (match result.internal_status with
   | InternalProgress ->
     result.internal_process.process_status == StepOk /\
     (exists (ev:local_event).
       is_internal ev /\
       local_process_correct
         system ev old_out out_bytes out_len
         received0 sent0 st0
         result.internal_process
         received1 sent1 st1
         wire_outputs local_outputs)
   | InternalFailed ->
     non_step_status result.internal_process.process_status /\
     (exists (ev:local_event).
       is_internal ev /\
       local_process_correct
         system ev old_out out_bytes out_len
         received0 sent0 st0
         result.internal_process
         received1 sent1 st1
         wire_outputs local_outputs)
   | InternalQuiescent ->
     ~ (pending st0) /\
     no_internal_step_enabled system is_internal st0 /\
     internal_no_progress
       old_out out_bytes received0 sent0 st0
       result received1 sent1 st1
       wire_outputs local_outputs
   | InternalBlocked ->
     pending st0 /\
     no_internal_step_enabled system is_internal st0 /\
     internal_no_progress
       old_out out_bytes received0 sent0 st0
       result received1 sent1 st1
       wire_outputs local_outputs)

(* A stepped or failed internal result refines the state machine exactly
   as the corresponding local result does.  Callers that already reason
   over [local_process_correct] need nothing new. *)
let lemma_internal_process_is_local_process
  (#state:Type0)
  (#wire_message:Type0)
  (#local_event:Type0)
  (#local_output:Type0)
  (system:WFSM.wire_format_state_machine state wire_message local_event local_output)
  (is_internal:local_event -> bool)
  (pending:state -> prop)
  (old_out out_bytes:TCP.bytes)
  (out_len:SZ.t)
  (received0 sent0:TCP.bytes)
  (st0:state)
  (result:internal_result)
  (received1 sent1:TCP.bytes)
  (st1:state)
  (wire_outputs:list wire_message)
  (local_outputs:list local_output)
  : Lemma
    (requires
      internal_process_correct
        system is_internal pending old_out out_bytes out_len
        received0 sent0 st0 result received1 sent1 st1
        wire_outputs local_outputs /\
      (result.internal_status == InternalProgress \/
       result.internal_status == InternalFailed))
    (ensures
      exists (ev:local_event).
        is_internal ev /\
        local_process_correct
          system ev old_out out_bytes out_len
          received0 sent0 st0
          result.internal_process
          received1 sent1 st1
          wire_outputs local_outputs)
= ()

(* Neither no-progress case moves the abstract state or the byte
   histories, so a scheduler may poll for internal progress freely
   without disturbing any refinement it has already established. *)
let lemma_internal_no_progress_preserves_state
  (#state:Type0)
  (#wire_message:Type0)
  (#local_event:Type0)
  (#local_output:Type0)
  (system:WFSM.wire_format_state_machine state wire_message local_event local_output)
  (is_internal:local_event -> bool)
  (pending:state -> prop)
  (old_out out_bytes:TCP.bytes)
  (out_len:SZ.t)
  (received0 sent0:TCP.bytes)
  (st0:state)
  (result:internal_result)
  (received1 sent1:TCP.bytes)
  (st1:state)
  (wire_outputs:list wire_message)
  (local_outputs:list local_output)
  : Lemma
    (requires
      internal_process_correct
        system is_internal pending old_out out_bytes out_len
        received0 sent0 st0 result received1 sent1 st1
        wire_outputs local_outputs /\
      (result.internal_status == InternalQuiescent \/
       result.internal_status == InternalBlocked))
    (ensures
      same_abstract_state received0 sent0 received1 sent1 st0 st1 /\
      Seq.equal out_bytes old_out /\
      result.internal_process.process_produced_len == 0sz)
= ()

(* ---------------------------------------------------------------- *)
(* Compatibility for protocols with no internal events.              *)
(*                                                                   *)
(* A protocol whose every local event comes from its caller sets      *)
(* [pi_internal] to [no_internal_events] and [pi_internal_pending] to *)
(* [nothing_pending].  Its [pi_process_internal] then returns         *)
(* [InternalQuiescent] unconditionally, discharged by the two lemmas  *)
(* below, and its behaviour is unchanged.                             *)
(* ---------------------------------------------------------------- *)

(* [inline_for_extraction] matters here.  This is a classifier that ignores
   its argument and returns a constant, but it returns [bool] rather than a
   ghost type, so without this KaRaMeL emits a monomorphized definition per
   instantiation whose parameter type is the protocol's local-event type.
   That type is specification-only and is not in any extraction bundle, so the
   emitted C referred to an undeclared type and failed to compile — see the
   TFTP and YMODEM verified-loop bundles, which do extract
   [Pulse.Lib.Protocol.Implementation].  Inlining folds the constant into any call
   site and emits nothing otherwise. *)
inline_for_extraction
let no_internal_events (#local_event:Type0) (_:local_event) : bool = false

let nothing_pending (#state:Type0) (_:state) : prop = False

let lemma_no_internal_events_never_enabled
  (#state:Type0)
  (#wire_message:Type0)
  (#local_event:Type0)
  (#local_output:Type0)
  (system:WFSM.wire_format_state_machine state wire_message local_event local_output)
  (st0:state)
  : Lemma
    (no_internal_step_enabled system (no_internal_events #local_event) st0)
= ()

let lemma_no_internal_events_quiescent
  (#state:Type0)
  (#wire_message:Type0)
  (#local_event:Type0)
  (#local_output:Type0)
  (system:WFSM.wire_format_state_machine state wire_message local_event local_output)
  (old_out out_bytes:TCP.bytes)
  (out_len:SZ.t)
  (received0 sent0:TCP.bytes)
  (st0:state)
  (result:internal_result)
  (received1 sent1:TCP.bytes)
  (st1:state)
  (wire_outputs:list wire_message)
  (local_outputs:list local_output)
  : Lemma
    (requires
      SZ.v out_len == Seq.length old_out /\
      Seq.length out_bytes == Seq.length old_out /\
      result.internal_status == InternalQuiescent /\
      internal_no_progress
        old_out out_bytes received0 sent0 st0
        result received1 sent1 st1
        wire_outputs local_outputs)
    (ensures
      internal_process_correct
        system
        (no_internal_events #local_event)
        (nothing_pending #state)
        old_out out_bytes out_len
        received0 sent0 st0 result received1 sent1 st1
        wire_outputs local_outputs)
= ()

(* The generic no-internal plumbing.  A protocol without internal events
   needs three more field values beyond [no_internal_events] and
   [nothing_pending]: two frame slprops and the processor itself.  All
   three are protocol-independent, so they are supplied once here rather
   than copied into every instance.

   The frames are [emp]: an internal step of such a protocol demands no
   resources and produces none, so whatever the caller holds is carried
   across by framing. *)

let no_internal_frame_pre
  (#local_frame #state:Type0)
  (_frame:local_frame)
  (_st0:state)
  (_out:array U8.t)
  (_out_len:SZ.t)
  (_old_out:TCP.bytes)
  : slprop =
  emp

let no_internal_frame_post
  (#local_frame #state #wire_message #local_output:Type0)
  (_frame:local_frame)
  (_result:internal_result)
  (_old_out:TCP.bytes)
  (_out_contents:TCP.bytes)
  (_st0:state)
  (_st1:state)
  (_wire_outputs:list wire_message)
  (_local_outputs:list local_output)
  : slprop =
  emp

(* The quiescent internal processor.  It reports [InternalQuiescent]
   unconditionally, which is sound because [no_internal_events] classifies
   nothing as internal and [nothing_pending] is [False]: there is never
   work for it to do.  Instances supply their own invariant and system as
   the first two arguments and partially apply. *)
fn quiescent_process_internal
  (#impl #state #wire_message #local_event #local_output #local_frame:Type0)
  (inv:impl -> TCP.bytes -> TCP.bytes -> state -> slprop)
  (system:impl ->
     GTot (WFSM.wire_format_state_machine state wire_message local_event local_output))
  (i:impl)
  (frame:local_frame)
  (out:array U8.t)
  (out_len:SZ.t)
  (received0:Ghost.erased TCP.bytes)
  (sent0:Ghost.erased TCP.bytes)
  (st0:Ghost.erased state)
  (old_out:Ghost.erased TCP.bytes)
requires
  inv i (Ghost.reveal received0) (Ghost.reveal sent0) (Ghost.reveal st0) **
  no_internal_frame_pre
    #local_frame #state
    frame
    (Ghost.reveal st0)
    out
    out_len
    (Ghost.reveal old_out) **
  pts_to out (Ghost.reveal old_out) **
  pure (SZ.v out_len == Seq.length (Ghost.reveal old_out))
returns result:internal_result
ensures exists* (received1:Ghost.erased TCP.bytes)
                (sent1:Ghost.erased TCP.bytes)
                (st1:Ghost.erased state)
                (out_contents:TCP.bytes)
                (wire_outputs:list wire_message)
                (local_outputs:list local_output).
  inv i (Ghost.reveal received1) (Ghost.reveal sent1) (Ghost.reveal st1) **
  no_internal_frame_post
    #local_frame #state #wire_message #local_output
    frame
    result
    (Ghost.reveal old_out)
    out_contents
    (Ghost.reveal st0)
    (Ghost.reveal st1)
    wire_outputs
    local_outputs **
  pts_to out out_contents **
  pure (
    internal_process_correct
      (system i)
      (no_internal_events #local_event)
      (nothing_pending #state)
      (Ghost.reveal old_out)
      out_contents
      out_len
      (Ghost.reveal received0)
      (Ghost.reveal sent0)
      (Ghost.reveal st0)
      result
      (Ghost.reveal received1)
      (Ghost.reveal sent1)
      (Ghost.reveal st1)
      wire_outputs
      local_outputs)
{
  let result : internal_result = {
    internal_status = InternalQuiescent;
    internal_process = {
      process_status = StepOk;
      process_consumed_len = 0sz;
      process_produced_len = 0sz;
      process_app_len = 0sz;
    };
  };
  unfold (no_internal_frame_pre
    #local_frame #state
    frame
    (Ghost.reveal st0)
    out
    out_len
    (Ghost.reveal old_out));
  fold (no_internal_frame_post
    #local_frame #state #wire_message #local_output
    frame
    result
    (Ghost.reveal old_out)
    (Ghost.reveal old_out)
    (Ghost.reveal st0)
    (Ghost.reveal st0)
    ([] <: list wire_message)
    ([] <: list local_output));
  lemma_no_internal_events_quiescent
    (system i)
    (Ghost.reveal old_out)
    (Ghost.reveal old_out)
    out_len
    (Ghost.reveal received0)
    (Ghost.reveal sent0)
    (Ghost.reveal st0)
    result
    (Ghost.reveal received0)
    (Ghost.reveal sent0)
    (Ghost.reveal st0)
    ([] <: list wire_message)
    ([] <: list local_output);
  result
}

noextract
class protocol_implementation
  (impl:Type0)
  (state:Type0)
  (wire_message:Type0)
  (local_event:Type0)
  (local_output:Type0)
  =
{
  pi_system:
    impl ->
      GTot (WFSM.wire_format_state_machine state wire_message local_event local_output);

  (* The internal subset of the local events (decision S1).  An event
     satisfying [pi_internal] is chosen by the implementation from its own
     state; it is never supplied by a caller, and [pi_process_local]
     refuses it. *)
  pi_internal:
    local_event ->
    bool;

  (* The implementation holds work that only an internal transition can
     discharge.  This is what separates [InternalQuiescent] (nothing
     pending, safe to read the network) from [InternalBlocked] (pending,
     but waiting on a local action).  A protocol without internal events
     sets this to [nothing_pending]. *)
  pi_internal_pending:
    state ->
    prop;

  pi_invariant:
    impl ->
    TCP.bytes ->
    TCP.bytes ->
    state ->
    slprop;

  pi_snapshot:
    impl ->
    TCP.bytes ->
    TCP.bytes ->
    state ->
    slprop;

  pi_network_frame:
    Type0;

  pi_network_frame_pre:
    pi_network_frame ->
    array U8.t ->
    SZ.t ->
    array U8.t ->
    SZ.t ->
    TCP.bytes ->
    TCP.bytes ->
    slprop;

  pi_network_frame_post:
    pi_network_frame ->
    process_result ->
    TCP.bytes ->
    SZ.t ->
    TCP.bytes ->
    TCP.bytes ->
    state ->
    state ->
    TCP.bytes ->
    list wire_message ->
    list local_output ->
    slprop;

  pi_local_frame:
    Type0;

  pi_local_frame_pre:
    local_event ->
    pi_local_frame ->
    state ->
    array U8.t ->
    SZ.t ->
    TCP.bytes ->
    slprop;

  pi_local_frame_post:
    local_event ->
    pi_local_frame ->
    process_result ->
    TCP.bytes ->
    TCP.bytes ->
    state ->
    state ->
    list wire_message ->
    list local_output ->
    slprop;

  (* Internal processing reuses [pi_local_frame]: an internal step needs
     the same output buffers as a local step.  It takes no event, because
     the event is determined by the state. *)
  pi_internal_frame_pre:
    pi_local_frame ->
    state ->
    array U8.t ->
    SZ.t ->
    TCP.bytes ->
    slprop;

  pi_internal_frame_post:
    pi_local_frame ->
    internal_result ->
    TCP.bytes ->
    TCP.bytes ->
    state ->
    state ->
    list wire_message ->
    list local_output ->
    slprop;

  pi_invariant_valid:
    i:impl ->
    received:Ghost.erased TCP.bytes ->
    sent:Ghost.erased TCP.bytes ->
    st:Ghost.erased state ->
      stt_ghost unit emp_inames
        (pi_invariant
          i
          (Ghost.reveal received)
          (Ghost.reveal sent)
          (Ghost.reveal st))
        (fun _ ->
          pi_invariant
            i
            (Ghost.reveal received)
            (Ghost.reveal sent)
            (Ghost.reveal st) **
          pure (
            WFSM.valid_byte_trace
              (pi_system i)
              (Ghost.reveal received)
              (Ghost.reveal st)
              (Ghost.reveal sent)
              Seq.empty));

  pi_take_snapshot:
    i:impl ->
    received:Ghost.erased TCP.bytes ->
    sent:Ghost.erased TCP.bytes ->
    st:Ghost.erased state ->
      stt_ghost unit emp_inames
        (pi_invariant
          i
          (Ghost.reveal received)
          (Ghost.reveal sent)
          (Ghost.reveal st))
        (fun _ ->
          pi_invariant
            i
            (Ghost.reveal received)
            (Ghost.reveal sent)
            (Ghost.reveal st) **
          pi_snapshot
            i
            (Ghost.reveal received)
            (Ghost.reveal sent)
            (Ghost.reveal st));

  pi_recall_snapshot:
    i:impl ->
    snapshot_received:Ghost.erased TCP.bytes ->
    snapshot_sent:Ghost.erased TCP.bytes ->
    snapshot_state:Ghost.erased state ->
    current_received:Ghost.erased TCP.bytes ->
    current_sent:Ghost.erased TCP.bytes ->
    current_state:Ghost.erased state ->
      stt_ghost unit emp_inames
        (pi_snapshot
          i
          (Ghost.reveal snapshot_received)
          (Ghost.reveal snapshot_sent)
          (Ghost.reveal snapshot_state) **
         pi_invariant
          i
          (Ghost.reveal current_received)
          (Ghost.reveal current_sent)
          (Ghost.reveal current_state))
        (fun _ ->
          pi_snapshot
            i
            (Ghost.reveal snapshot_received)
            (Ghost.reveal snapshot_sent)
            (Ghost.reveal snapshot_state) **
          pi_invariant
            i
            (Ghost.reveal current_received)
            (Ghost.reveal current_sent)
            (Ghost.reveal current_state) **
          pure (
            state_ahead
              (pi_system i)
              (Ghost.reveal snapshot_state)
              (Ghost.reveal current_state) /\
            histories_ahead
              (Ghost.reveal snapshot_received)
              (Ghost.reveal snapshot_sent)
              (Ghost.reveal current_received)
              (Ghost.reveal current_sent)));

  pi_process_network:
    i:impl ->
    frame:pi_network_frame ->
    input:array U8.t ->
    input_len:SZ.t ->
    out:array U8.t ->
    out_len:SZ.t ->
    received0:Ghost.erased TCP.bytes ->
    sent0:Ghost.erased TCP.bytes ->
    st0:Ghost.erased state ->
    input_contents:Ghost.erased TCP.bytes ->
    old_out:Ghost.erased TCP.bytes ->
      stt process_result
        (pi_invariant
          i
          (Ghost.reveal received0)
          (Ghost.reveal sent0)
          (Ghost.reveal st0) **
          pi_network_frame_pre
            frame
            input
            input_len
            out
            out_len
            (Ghost.reveal input_contents)
            (Ghost.reveal old_out) **
         pts_to input (Ghost.reveal input_contents) **
         pts_to out (Ghost.reveal old_out) **
         pure (
          buffers_wf
            (Ghost.reveal input_contents)
            input_len
            (Ghost.reveal old_out)
            out_len))
        (fun result ->
          exists* (received1:Ghost.erased TCP.bytes)
                  (sent1:Ghost.erased TCP.bytes)
                  (st1:Ghost.erased state)
                  (out_contents:TCP.bytes)
                  (consumed:TCP.bytes)
                  (wire_outputs:list wire_message)
                  (local_outputs:list local_output).
            pi_invariant
              i
              (Ghost.reveal received1)
              (Ghost.reveal sent1)
              (Ghost.reveal st1) **
            pi_network_frame_post
              frame
              result
              (Ghost.reveal input_contents)
              input_len
              (Ghost.reveal old_out)
              out_contents
              (Ghost.reveal st0)
              (Ghost.reveal st1)
              consumed
              wire_outputs
              local_outputs **
            pts_to input (Ghost.reveal input_contents) **
            pts_to out out_contents **
            pure (
              network_process_correct
                (pi_system i)
                (Ghost.reveal input_contents)
                input_len
                (Ghost.reveal old_out)
                out_contents
                out_len
                (Ghost.reveal received0)
                (Ghost.reveal sent0)
                (Ghost.reveal st0)
                result
                (Ghost.reveal received1)
                (Ghost.reveal sent1)
                (Ghost.reveal st1)
                consumed
                wire_outputs
                local_outputs));

  pi_process_local:
    i:impl ->
    ev:local_event ->
    frame:pi_local_frame ->
    out:array U8.t ->
    out_len:SZ.t ->
    received0:Ghost.erased TCP.bytes ->
    sent0:Ghost.erased TCP.bytes ->
    st0:Ghost.erased state ->
    old_out:Ghost.erased TCP.bytes ->
      stt process_result
        (pi_invariant
          i
          (Ghost.reveal received0)
          (Ghost.reveal sent0)
          (Ghost.reveal st0) **
         pi_local_frame_pre
           ev
           frame
           (Ghost.reveal st0)
           out
           out_len
           (Ghost.reveal old_out) **
         pts_to out (Ghost.reveal old_out) **
         pure (
           SZ.v out_len == Seq.length (Ghost.reveal old_out) /\
           ~ (pi_internal ev)))
        (fun result ->
          exists* (received1:Ghost.erased TCP.bytes)
                  (sent1:Ghost.erased TCP.bytes)
                  (st1:Ghost.erased state)
                  (out_contents:TCP.bytes)
                  (wire_outputs:list wire_message)
                  (local_outputs:list local_output).
            pi_invariant
              i
              (Ghost.reveal received1)
              (Ghost.reveal sent1)
              (Ghost.reveal st1) **
            pi_local_frame_post
              ev
              frame
              result
              (Ghost.reveal old_out)
              out_contents
              (Ghost.reveal st0)
              (Ghost.reveal st1)
              wire_outputs
              local_outputs **
            pts_to out out_contents **
            pure (
              local_process_correct
                (pi_system i)
                ev
                (Ghost.reveal old_out)
                out_contents
                out_len
                (Ghost.reveal received0)
                (Ghost.reveal sent0)
                (Ghost.reveal st0)
                result
                (Ghost.reveal received1)
                (Ghost.reveal sent1)
                (Ghost.reveal st1)
                wire_outputs
                local_outputs));

  (* Make one step of internal progress, if any is available.

     This is the operation a scheduler polls between network reads.  It is
     total: it always returns, reporting through [internal_status] whether
     it stepped, whether it is quiescent, whether it is blocked on a local
     action, or whether the pending work is unprocessable.  Only
     [InternalProgress] and [InternalFailed] move the abstract state; the
     other two are observably no-ops, so polling is free. *)
  pi_process_internal:
    i:impl ->
    frame:pi_local_frame ->
    out:array U8.t ->
    out_len:SZ.t ->
    received0:Ghost.erased TCP.bytes ->
    sent0:Ghost.erased TCP.bytes ->
    st0:Ghost.erased state ->
    old_out:Ghost.erased TCP.bytes ->
      stt internal_result
        (pi_invariant
          i
          (Ghost.reveal received0)
          (Ghost.reveal sent0)
          (Ghost.reveal st0) **
         pi_internal_frame_pre
           frame
           (Ghost.reveal st0)
           out
           out_len
           (Ghost.reveal old_out) **
         pts_to out (Ghost.reveal old_out) **
         pure (SZ.v out_len == Seq.length (Ghost.reveal old_out)))
        (fun result ->
          exists* (received1:Ghost.erased TCP.bytes)
                  (sent1:Ghost.erased TCP.bytes)
                  (st1:Ghost.erased state)
                  (out_contents:TCP.bytes)
                  (wire_outputs:list wire_message)
                  (local_outputs:list local_output).
            pi_invariant
              i
              (Ghost.reveal received1)
              (Ghost.reveal sent1)
              (Ghost.reveal st1) **
            pi_internal_frame_post
              frame
              result
              (Ghost.reveal old_out)
              out_contents
              (Ghost.reveal st0)
              (Ghost.reveal st1)
              wire_outputs
              local_outputs **
            pts_to out out_contents **
            pure (
              internal_process_correct
                (pi_system i)
                pi_internal
                pi_internal_pending
                (Ghost.reveal old_out)
                out_contents
                out_len
                (Ghost.reveal received0)
                (Ghost.reveal sent0)
                (Ghost.reveal st0)
                result
                (Ghost.reveal received1)
                (Ghost.reveal sent1)
                (Ghost.reveal st1)
                wire_outputs
                local_outputs));
}
