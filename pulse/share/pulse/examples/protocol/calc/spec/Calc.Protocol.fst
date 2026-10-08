module Calc.Protocol

module L = FStar.List.Tot
module Seq = FStar.Seq
module SP = FStar.Seq.Properties
module SM = Pulse.Lib.Protocol.StateMachine
module TCP = Pulse.Lib.TCP
module WF = Pulse.Lib.Protocol.WireFormat
module WFSM = Pulse.Lib.Protocol.WireFormatStateMachine

open FStar.List.Tot
open Calc.Wire
open Calc.Spec
open Calc.Log

type calc_frame = b:bytes {
  Seq.length b == 5 /\
  parse_request b <> None
}

type calc_frame_local_event =
  | CalcFrameLocalNoop

let calc_serialize_frame
  (msg:calc_frame)
  : GTot TCP.bytes =
  msg

let calc_parse_frame
  (input:TCP.bytes)
  : GTot (WF.parse_result calc_frame) =
  if 5 <= Seq.length input then
    let msg = Seq.slice input 0 5 in
    if parse_request msg <> None then
      Some (msg, Seq.slice input 5 (Seq.length input))
    else
      None
  else
    None

let calc_response_frame
  (resp:response)
  : calc_frame =
  serialize_response resp

let calc_frame_request
  (msg:calc_frame)
  : request =
  match parse_request msg with
  | Some req -> req
  | None -> Peek

let calc_frame_residual_after_prefix
  (msg:calc_frame)
  (rest:TCP.bytes)
  : TCP.bytes =
  Seq.slice (Seq.append msg rest) 5 (Seq.length (Seq.append msg rest))

let lemma_slice_full_5
  (msg:bytes{Seq.length msg == 5})
  : Lemma
      (ensures Seq.equal (Seq.slice msg 0 5) msg)
=
  Seq.lemma_len_slice msg 0 5;
  assert (forall (i:nat{i < Seq.length (Seq.slice msg 0 5)}).
    Seq.index (Seq.slice msg 0 5) i == Seq.index msg i);
  Seq.lemma_eq_intro (Seq.slice msg 0 5) msg

let lemma_calc_frame_parse_prefix_shape
  (msg:calc_frame)
  (rest:TCP.bytes)
  : Lemma
      (ensures
        Seq.equal (Seq.slice (Seq.append msg rest) 0 5) msg /\
        Seq.equal (calc_frame_residual_after_prefix msg rest) rest)
=
  Calc.Log.lemma_slice_append_prefix msg rest;
  lemma_slice_full_5 msg;
  Seq.lemma_eq_elim (Seq.slice msg 0 5) msg;
  assert (Seq.equal (Seq.slice (Seq.append msg rest) 0 5) msg);
  SP.append_slices msg rest;
  assert (Seq.equal rest (calc_frame_residual_after_prefix msg rest))

let lemma_calc_parse_serialize_exact
  (msg:calc_frame)
  : Lemma
      (ensures
        exists parsed.
          calc_parse_frame (calc_serialize_frame msg) ==
            Some (parsed, Seq.empty) /\
          parsed == msg)
=
  lemma_slice_full_5 msg;
  assert (Seq.equal (Seq.slice msg 0 5) msg);
  Seq.lemma_eq_elim (Seq.slice msg 0 5) msg;
  Seq.lemma_len_slice msg 5 5;
  assert (Seq.equal (Seq.slice msg 5 (Seq.length msg)) Seq.empty);
  assert (calc_parse_frame (calc_serialize_frame msg) ==
    Some (msg, Seq.empty))

let lemma_calc_parse_serialize_prefix
  (msg:calc_frame)
  (rest:TCP.bytes)
  : Lemma
      (ensures
        exists parsed.
          calc_parse_frame
            (Seq.append (calc_serialize_frame msg) rest) ==
              Some (parsed, rest) /\
          parsed == msg)
=
  lemma_calc_frame_parse_prefix_shape msg rest;
  assert (Seq.equal (Seq.slice (Seq.append msg rest) 0 5) msg);
  assert (Seq.equal (calc_frame_residual_after_prefix msg rest) rest);
  Seq.lemma_eq_elim (Seq.slice (Seq.append msg rest) 0 5) msg;
  Seq.lemma_eq_elim (calc_frame_residual_after_prefix msg rest) rest;
  assert (calc_parse_frame
    (Seq.append (calc_serialize_frame msg) rest) == Some (msg, rest))

noextract
let calc_frame_wire_format : WF.wire_format calc_frame =
{
  WF.wf_serialize = calc_serialize_frame;
  WF.wf_parse = calc_parse_frame;
  WF.wf_parse_serialize_exact = lemma_calc_parse_serialize_exact;
  }

noextract
let calc_frame_wire_format_stream_laws :
  WF.wire_format_stream_laws calc_frame calc_frame_wire_format =
  {
    WF.wfsl_parse_serialize_prefix = lemma_calc_parse_serialize_prefix;
  }

let calc_frame_step
  (log0:calc_log)
  (ev:SM.event calc_frame calc_frame_local_event)
  (log1:calc_log)
  (output:SM.step_output calc_frame unit)
  : GTot prop =
  match ev with
  | SM.WireEvent msg ->
    let req = calc_frame_request msg in
    let (next_stack, resp) = step log0.current_state req in
    let resp_msg = calc_response_frame resp in
    log1.current_state == next_stack /\
    log1.requests == log0.requests @ [req] /\
    log1.responses == log0.responses @ [resp] /\
    Seq.equal log1.input_bytes (Seq.append log0.input_bytes msg) /\
    Seq.equal log1.output_bytes (Seq.append log0.output_bytes resp_msg) /\
    output.SM.so_wire_outputs == [resp_msg] /\
    output.SM.so_local_outputs == []
  | SM.LocalEvent CalcFrameLocalNoop ->
    log1 == log0 /\
    output.SM.so_wire_outputs == [] /\
    output.SM.so_local_outputs == []

let calc_frame_response_for
  (log0:calc_log)
  (msg:calc_frame)
  : calc_frame =
  let req = calc_frame_request msg in
  let (_next_stack, resp) = step log0.current_state req in
  calc_response_frame resp

let calc_frame_network_step_ok
  (log0:calc_log)
  (msg:calc_frame)
  (log1:calc_log)
  (actual_output:bytes)
  : prop =
  let response_msg = calc_frame_response_for log0 msg in
  calc_frame_step
    log0
    (SM.WireEvent msg)
    log1
    {
      SM.so_wire_outputs = [response_msg];
      SM.so_local_outputs = [];
    } /\
  Seq.equal response_msg actual_output

#push-options "--fuel 2 --ifuel 2 --z3rlimit 10"

let lemma_seq_equal_keep
  (#a:Type0)
  (s0 s1:Seq.seq a)
  : Lemma
      (requires Seq.equal s0 s1)
      (ensures Seq.equal s0 s1)
=
  ()

let rec lemma_calc_serialize_all_append
  (msgs0:list calc_frame)
  (msgs1:list calc_frame)
  : Lemma
      (ensures
        Seq.equal
          (WF.serialize_all calc_frame_wire_format (L.append msgs0 msgs1))
          (Seq.append
            (WF.serialize_all calc_frame_wire_format msgs0)
            (WF.serialize_all calc_frame_wire_format msgs1)))
      (decreases msgs0)
=
  match msgs0 with
  | [] ->
    assert (Seq.equal
      (WF.serialize_all calc_frame_wire_format msgs1)
      (Seq.append Seq.empty (WF.serialize_all calc_frame_wire_format msgs1)));
    lemma_seq_equal_keep
      (WF.serialize_all calc_frame_wire_format (L.append [] msgs1))
      (Seq.append
        (WF.serialize_all calc_frame_wire_format [])
        (WF.serialize_all calc_frame_wire_format msgs1))
  | msg :: rest ->
    lemma_calc_serialize_all_append rest msgs1;
    Seq.lemma_eq_elim
      (WF.serialize_all calc_frame_wire_format (L.append rest msgs1))
      (Seq.append
        (WF.serialize_all calc_frame_wire_format rest)
        (WF.serialize_all calc_frame_wire_format msgs1));
    Seq.append_assoc
      (calc_serialize_frame msg)
      (WF.serialize_all calc_frame_wire_format rest)
      (WF.serialize_all calc_frame_wire_format msgs1);
    assert (Seq.equal
      (WF.serialize_all calc_frame_wire_format (L.append (msg :: rest) msgs1))
      (Seq.append
        (WF.serialize_all calc_frame_wire_format (msg :: rest))
        (WF.serialize_all calc_frame_wire_format msgs1)));
    lemma_seq_equal_keep
      (WF.serialize_all calc_frame_wire_format (L.append (msg :: rest) msgs1))
      (Seq.append
        (WF.serialize_all calc_frame_wire_format (msg :: rest))
        (WF.serialize_all calc_frame_wire_format msgs1))

let rec lemma_calc_trace_input_bytes_append_one
  (trace:list (SM.transition calc_log calc_frame calc_frame_local_event unit))
  (tr:SM.transition calc_log calc_frame calc_frame_local_event unit)
  : Lemma
      (ensures
        Seq.equal
          (WF.serialize_all calc_frame_wire_format (WFSM.trace_input_messages (L.append trace [tr])))
          (Seq.append
            (WF.serialize_all calc_frame_wire_format (WFSM.trace_input_messages trace))
            (WF.serialize_all calc_frame_wire_format (WFSM.event_input_messages tr.SM.tr_event))))
      (decreases trace)
=
  match trace with
  | [] ->
    lemma_calc_serialize_all_append (WFSM.event_input_messages tr.SM.tr_event) [];
    Seq.lemma_eq_elim
      (WF.serialize_all calc_frame_wire_format (L.append (WFSM.event_input_messages tr.SM.tr_event) []))
      (Seq.append
        (WF.serialize_all calc_frame_wire_format (WFSM.event_input_messages tr.SM.tr_event))
        (WF.serialize_all calc_frame_wire_format []));
    lemma_seq_equal_keep
      (WF.serialize_all calc_frame_wire_format (WFSM.trace_input_messages (L.append trace [tr])))
      (Seq.append
        (WF.serialize_all calc_frame_wire_format (WFSM.trace_input_messages trace))
        (WF.serialize_all calc_frame_wire_format (WFSM.event_input_messages tr.SM.tr_event)))
  | hd :: rest ->
    lemma_calc_trace_input_bytes_append_one rest tr;
    assert (
      WFSM.trace_input_messages (L.append (hd :: rest) [tr]) ==
      L.append
        (WFSM.event_input_messages hd.SM.tr_event)
        (WFSM.trace_input_messages (L.append rest [tr])));
    lemma_calc_serialize_all_append
      (WFSM.event_input_messages hd.SM.tr_event)
      (WFSM.trace_input_messages (L.append rest [tr]));
    lemma_calc_serialize_all_append
      (WFSM.event_input_messages hd.SM.tr_event)
      (WFSM.trace_input_messages rest);
    Seq.lemma_eq_elim
      (WF.serialize_all calc_frame_wire_format
        (L.append
          (WFSM.event_input_messages hd.SM.tr_event)
          (WFSM.trace_input_messages (L.append rest [tr]))))
      (Seq.append
        (WF.serialize_all calc_frame_wire_format (WFSM.event_input_messages hd.SM.tr_event))
        (WF.serialize_all calc_frame_wire_format (WFSM.trace_input_messages (L.append rest [tr]))));
    Seq.lemma_eq_elim
      (WF.serialize_all calc_frame_wire_format
        (L.append
          (WFSM.event_input_messages hd.SM.tr_event)
          (WFSM.trace_input_messages rest)))
      (Seq.append
        (WF.serialize_all calc_frame_wire_format (WFSM.event_input_messages hd.SM.tr_event))
        (WF.serialize_all calc_frame_wire_format (WFSM.trace_input_messages rest)));
    Seq.lemma_eq_elim
      (WF.serialize_all calc_frame_wire_format (WFSM.trace_input_messages (L.append rest [tr])))
      (Seq.append
        (WF.serialize_all calc_frame_wire_format (WFSM.trace_input_messages rest))
        (WF.serialize_all calc_frame_wire_format (WFSM.event_input_messages tr.SM.tr_event)));
    Seq.append_assoc
      (WF.serialize_all calc_frame_wire_format (WFSM.event_input_messages hd.SM.tr_event))
      (WF.serialize_all calc_frame_wire_format (WFSM.trace_input_messages rest))
      (WF.serialize_all calc_frame_wire_format (WFSM.event_input_messages tr.SM.tr_event));
    assert (
      Seq.append
        (WF.serialize_all calc_frame_wire_format (WFSM.event_input_messages hd.SM.tr_event))
        (Seq.append
          (WF.serialize_all calc_frame_wire_format (WFSM.trace_input_messages rest))
          (WF.serialize_all calc_frame_wire_format (WFSM.event_input_messages tr.SM.tr_event))) ==
      Seq.append
        (Seq.append
          (WF.serialize_all calc_frame_wire_format (WFSM.event_input_messages hd.SM.tr_event))
          (WF.serialize_all calc_frame_wire_format (WFSM.trace_input_messages rest)))
        (WF.serialize_all calc_frame_wire_format (WFSM.event_input_messages tr.SM.tr_event)));
    Seq.lemma_eq_refl
      (WF.serialize_all calc_frame_wire_format (WFSM.trace_input_messages (L.append (hd :: rest) [tr])))
      (Seq.append
        (WF.serialize_all calc_frame_wire_format (WFSM.trace_input_messages (hd :: rest)))
        (WF.serialize_all calc_frame_wire_format (WFSM.event_input_messages tr.SM.tr_event)));
    assert (Seq.equal
      (WF.serialize_all calc_frame_wire_format (WFSM.trace_input_messages (L.append trace [tr])))
      (Seq.append
        (WF.serialize_all calc_frame_wire_format (WFSM.trace_input_messages trace))
        (WF.serialize_all calc_frame_wire_format (WFSM.event_input_messages tr.SM.tr_event))));
    lemma_seq_equal_keep
      (WF.serialize_all calc_frame_wire_format (WFSM.trace_input_messages (L.append trace [tr])))
      (Seq.append
        (WF.serialize_all calc_frame_wire_format (WFSM.trace_input_messages trace))
        (WF.serialize_all calc_frame_wire_format (WFSM.event_input_messages tr.SM.tr_event)))

val lemma_calc_trace_wire_bytes_append_one
  (trace:list (SM.transition calc_log calc_frame calc_frame_local_event unit))
  (tr:SM.transition calc_log calc_frame calc_frame_local_event unit)
  : Lemma
      (ensures
        Seq.equal
          (WF.serialize_all calc_frame_wire_format (SM.trace_wire_outputs (L.append trace [tr])))
          (Seq.append
            (WF.serialize_all calc_frame_wire_format (SM.trace_wire_outputs trace))
            (WF.serialize_all calc_frame_wire_format tr.SM.tr_output.SM.so_wire_outputs)))
      (decreases trace)

let rec lemma_calc_trace_wire_bytes_append_one trace tr =
  match trace with
  | [] ->
    lemma_calc_serialize_all_append tr.SM.tr_output.SM.so_wire_outputs [];
    Seq.lemma_eq_elim
      (WF.serialize_all calc_frame_wire_format (L.append tr.SM.tr_output.SM.so_wire_outputs []))
      (Seq.append
        (WF.serialize_all calc_frame_wire_format tr.SM.tr_output.SM.so_wire_outputs)
        (WF.serialize_all calc_frame_wire_format []));
    lemma_seq_equal_keep
      (WF.serialize_all calc_frame_wire_format (SM.trace_wire_outputs (L.append trace [tr])))
      (Seq.append
        (WF.serialize_all calc_frame_wire_format (SM.trace_wire_outputs trace))
        (WF.serialize_all calc_frame_wire_format tr.SM.tr_output.SM.so_wire_outputs))
  | hd :: rest ->
    lemma_calc_trace_wire_bytes_append_one rest tr;
    assert (
      SM.trace_wire_outputs (L.append (hd :: rest) [tr]) ==
      L.append
        hd.SM.tr_output.SM.so_wire_outputs
        (SM.trace_wire_outputs (L.append rest [tr])));
    lemma_calc_serialize_all_append
      hd.SM.tr_output.SM.so_wire_outputs
      (SM.trace_wire_outputs (L.append rest [tr]));
    lemma_calc_serialize_all_append
      hd.SM.tr_output.SM.so_wire_outputs
      (SM.trace_wire_outputs rest);
    Seq.lemma_eq_elim
      (WF.serialize_all calc_frame_wire_format
        (L.append
          hd.SM.tr_output.SM.so_wire_outputs
          (SM.trace_wire_outputs (L.append rest [tr]))))
      (Seq.append
        (WF.serialize_all calc_frame_wire_format hd.SM.tr_output.SM.so_wire_outputs)
        (WF.serialize_all calc_frame_wire_format (SM.trace_wire_outputs (L.append rest [tr]))));
    Seq.lemma_eq_elim
      (WF.serialize_all calc_frame_wire_format
        (L.append
          hd.SM.tr_output.SM.so_wire_outputs
          (SM.trace_wire_outputs rest)))
      (Seq.append
        (WF.serialize_all calc_frame_wire_format hd.SM.tr_output.SM.so_wire_outputs)
        (WF.serialize_all calc_frame_wire_format (SM.trace_wire_outputs rest)));
    Seq.lemma_eq_elim
      (WF.serialize_all calc_frame_wire_format (SM.trace_wire_outputs (L.append rest [tr])))
      (Seq.append
        (WF.serialize_all calc_frame_wire_format (SM.trace_wire_outputs rest))
        (WF.serialize_all calc_frame_wire_format tr.SM.tr_output.SM.so_wire_outputs));
    Seq.append_assoc
      (WF.serialize_all calc_frame_wire_format hd.SM.tr_output.SM.so_wire_outputs)
      (WF.serialize_all calc_frame_wire_format (SM.trace_wire_outputs rest))
      (WF.serialize_all calc_frame_wire_format tr.SM.tr_output.SM.so_wire_outputs);
    assert (
      Seq.append
        (WF.serialize_all calc_frame_wire_format hd.SM.tr_output.SM.so_wire_outputs)
        (Seq.append
          (WF.serialize_all calc_frame_wire_format (SM.trace_wire_outputs rest))
          (WF.serialize_all calc_frame_wire_format tr.SM.tr_output.SM.so_wire_outputs)) ==
      Seq.append
        (Seq.append
          (WF.serialize_all calc_frame_wire_format hd.SM.tr_output.SM.so_wire_outputs)
          (WF.serialize_all calc_frame_wire_format (SM.trace_wire_outputs rest)))
        (WF.serialize_all calc_frame_wire_format tr.SM.tr_output.SM.so_wire_outputs));
    Seq.lemma_eq_refl
      (WF.serialize_all calc_frame_wire_format (SM.trace_wire_outputs (L.append (hd :: rest) [tr])))
      (Seq.append
        (WF.serialize_all calc_frame_wire_format (SM.trace_wire_outputs (hd :: rest)))
        (WF.serialize_all calc_frame_wire_format tr.SM.tr_output.SM.so_wire_outputs));
    assert (Seq.equal
      (WF.serialize_all calc_frame_wire_format (SM.trace_wire_outputs (L.append trace [tr])))
      (Seq.append
        (WF.serialize_all calc_frame_wire_format (SM.trace_wire_outputs trace))
        (WF.serialize_all calc_frame_wire_format tr.SM.tr_output.SM.so_wire_outputs)));
    lemma_seq_equal_keep
      (WF.serialize_all calc_frame_wire_format (SM.trace_wire_outputs (L.append trace [tr])))
      (Seq.append
        (WF.serialize_all calc_frame_wire_format (SM.trace_wire_outputs trace))
        (WF.serialize_all calc_frame_wire_format tr.SM.tr_output.SM.so_wire_outputs))

#pop-options

noextract
let calc_frame_state_machine
  : SM.state_machine calc_log calc_frame calc_frame_local_event unit =
  {
    SM.sm_initial_state = initial_log;
    SM.sm_step = calc_frame_step;
  }

noextract
let calc_frame_wire_format_state_machine
  : WFSM.wire_format_state_machine calc_log calc_frame calc_frame_local_event unit =
  {
    WFSM.wfsm_state_machine = calc_frame_state_machine;
    WFSM.wfsm_wire_format = calc_frame_wire_format;
  }
