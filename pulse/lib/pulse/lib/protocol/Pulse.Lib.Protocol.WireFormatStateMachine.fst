module Pulse.Lib.Protocol.WireFormatStateMachine

module L = FStar.List.Tot
module Seq = FStar.Seq
module SM = Pulse.Lib.Protocol.StateMachine
module TCP = Pulse.Lib.TCP.History
module WF = Pulse.Lib.Protocol.WireFormat

noextract
class wire_format_state_machine
  (state:Type0)
  (wire_message:Type0)
  (local_event:Type0)
  (local_output:Type0)
  =
{
  wfsm_state_machine:
    SM.state_machine state wire_message local_event local_output;

  wfsm_wire_format:
    WF.wire_format wire_message;
}

let event_input_messages
  (#wire_message:Type0)
  (#local_event:Type0)
  (ev:SM.event wire_message local_event)
  : list wire_message =
  match ev with
  | SM.WireEvent msg -> [msg]
  | SM.LocalEvent _ -> []

let rec trace_input_messages
  (#state:Type0)
  (#wire_message:Type0)
  (#local_event:Type0)
  (#local_output:Type0)
  (trace:list (SM.transition state wire_message local_event local_output))
  : Tot (list wire_message)
        (decreases trace)
=
  match trace with
  | [] -> []
  | tr :: rest ->
    L.append (event_input_messages tr.SM.tr_event) (trace_input_messages rest)

let valid_byte_trace
  (#state:Type0)
  (#wire_message:Type0)
  (#local_event:Type0)
  (#local_output:Type0)
  (system:wire_format_state_machine state wire_message local_event local_output)
  (input_bytes:TCP.bytes)
  (st1:state)
  (output_bytes:TCP.bytes)
  (residual_input:TCP.bytes)
  : GTot prop =
  exists trace.
    SM.trace_reaches
      system.wfsm_state_machine
      system.wfsm_state_machine.SM.sm_initial_state
      trace
      st1 /\
    (* The received bytes refine the trace's input messages.  Two refinements are
       accepted, so the class serves BOTH stream and datagram transports:

         * STREAM (strong-prefix wire formats, e.g. YMODEM/FTP-block): the byte
           stream greedily re-parses, message by message, into the trace inputs
           (`parses_as`).  This recovers the message boundaries from the bytes
           alone — available only when every consumed message is a strong-prefix
           parser.

         * DATAGRAM (datagram-delimited wire formats, e.g. IETF TFTP): the byte
           stream is exactly the serialization of the trace inputs.  Here the
           message boundaries come from the transport framing (one datagram per
           `read`), NOT from the bytes, so a non-strong-prefix message (TFTP's
           implicit-length DATA payload) is admissible.  This is the faithful
           refinement for a datagram protocol whose payload length is supplied by
           the UDP datagram boundary.

       The output side is always a serialize-equality (below); making the input
       side a disjunction is a WEAKENING, so every existing strong-prefix instance
       that proved the `parses_as` disjunct still satisfies this predicate
       unchanged. *)
    (WF.parses_as
       system.wfsm_wire_format
       input_bytes
       (trace_input_messages trace)
       residual_input
     \/
     Seq.equal
       input_bytes
       (Seq.append
         (WF.serialize_all
           system.wfsm_wire_format
           (trace_input_messages trace))
         residual_input)) /\
    Seq.equal
      output_bytes
      (WF.serialize_all
        system.wfsm_wire_format
        (SM.trace_wire_outputs trace))

let trace_local_outputs
  (#state:Type0)
  (#wire_message:Type0)
  (#local_event:Type0)
  (#local_output:Type0)
  (trace:list (SM.transition state wire_message local_event local_output))
  : Tot (list local_output) =
  SM.trace_local_outputs trace

let lemma_serialized_trace_inputs_refine_bytes
  (#state:Type0)
  (#wire_message:Type0)
  (#local_event:Type0)
  (#local_output:Type0)
  (system:wire_format_state_machine state wire_message local_event local_output)
  (laws:WF.wire_format_stream_laws wire_message system.wfsm_wire_format)
  (st0:state)
  (trace:list (SM.transition state wire_message local_event local_output))
  (st1:state)
  (residual_input:TCP.bytes)
  : Lemma
      (requires
        SM.trace_reaches system.wfsm_state_machine st0 trace st1)
      (ensures
        st0 == system.wfsm_state_machine.SM.sm_initial_state ==>
        valid_byte_trace
          system
          (WF.serialize_with_tail
            system.wfsm_wire_format
            (trace_input_messages trace)
            residual_input)
          st1
          (WF.serialize_all
            system.wfsm_wire_format
            (SM.trace_wire_outputs trace))
          residual_input)
=
  WF.lemma_parse_serialize_with_tail_inverse
    system.wfsm_wire_format
    laws
    (trace_input_messages trace)
    residual_input;
  assert (WF.parses_as
    system.wfsm_wire_format
    (WF.serialize_with_tail
      system.wfsm_wire_format
      (trace_input_messages trace)
      residual_input)
    (trace_input_messages trace)
    residual_input);
  assert (Seq.equal
    (WF.serialize_all
      system.wfsm_wire_format
      (SM.trace_wire_outputs trace))
    (WF.serialize_all
      system.wfsm_wire_format
    (SM.trace_wire_outputs trace)));
  if st0 == system.wfsm_state_machine.SM.sm_initial_state then
    assert (exists trace'.
    SM.trace_reaches
      system.wfsm_state_machine
      system.wfsm_state_machine.SM.sm_initial_state
      trace'
      st1 /\
    WF.parses_as
      system.wfsm_wire_format
      (WF.serialize_with_tail
        system.wfsm_wire_format
        (trace_input_messages trace)
        residual_input)
      (trace_input_messages trace')
      residual_input /\
    Seq.equal
      (WF.serialize_all
        system.wfsm_wire_format
        (SM.trace_wire_outputs trace))
      (WF.serialize_all
        system.wfsm_wire_format
        (SM.trace_wire_outputs trace')))
