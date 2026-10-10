module Pulse.Lib.Protocol.Endpoint

#lang-pulse

open Pulse.Lib.Pervasives

module CPI = Pulse.Lib.Protocol.Implementation
module Seq = FStar.Seq
module SZ = FStar.SizeT
module TCP = Pulse.Lib.TCP
module U8 = FStar.UInt8

// Driver-facing endpoint contract for first-order protocol implementations.
//
// The core protocol implementation proves that network/local handlers refine a
// wire-format state machine. This endpoint layer adds the executable scheduling
// and resource story needed by a TCP driver: persistent endpoint frames,
// branch-specific network/local frames, concrete I/O buffers, and finish hooks
// that reassemble the invariant after a handler runs. There is deliberately no
// external-action branch; endpoint instances turn callback results into ordinary
// local/API events before the driver sees them.
type endpoint_action
  (network_frame:Type0)
  (local_event:Type0)
  (local_frame:Type0)
  =
  | EndpointNeedInput:
      frame:network_frame ->
        endpoint_action network_frame local_event local_frame
  | EndpointLocal:
      ev:local_event ->
      frame:local_frame ->
        endpoint_action network_frame local_event local_frame
  | EndpointDone:
        endpoint_action network_frame local_event local_frame
  | EndpointFailed:
        endpoint_action network_frame local_event local_frame

[@@pulse_unfold]
let network_buffers
  (input:array U8.t)
  (input_len:SZ.t)
  (out:array U8.t)
  (out_len:SZ.t)
  (input_contents:TCP.bytes)
  (old_out:TCP.bytes)
  : slprop =
  pts_to input input_contents **
  pts_to out old_out **
  pure (
    SZ.v input_len <= Seq.length input_contents /\
    Seq.length old_out == SZ.v out_len)

[@@pulse_unfold]
let local_output_buffer
  (out:array U8.t)
  (out_len:SZ.t)
  (old_out:TCP.bytes)
  : slprop =
  pts_to out old_out **
  pure (Seq.length old_out == SZ.v out_len)

(* An endpoint may never hand an INTERNAL event to the driver.  Internal
   events are chosen by the implementation from its own state and are
   discharged by [pi_process_internal]; routing one through the local path
   would let a caller step the implementation past buffered work it has
   not yet accounted for.  [pi_process_local] refuses such an event, and
   this predicate is where the endpoint discharges that obligation. *)
let action_not_internal
  (#impl:Type0)
  (#state:Type0)
  (#wire_message:Type0)
  (#local_event:Type0)
  (#local_output:Type0)
  (protocol:CPI.protocol_implementation
    impl
    state
    wire_message
    local_event
    local_output)
  (action:endpoint_action
    protocol.CPI.pi_network_frame
    local_event
    protocol.CPI.pi_local_frame)
  : prop =
  match action with
  | EndpointLocal ev _ -> ~ (protocol.CPI.pi_internal ev)
  | _ -> True

noextract
class protocol_endpoint
  (impl:Type0)
  (state:Type0)
  (wire_message:Type0)
  (local_event:Type0)
  (local_output:Type0)
  (protocol:CPI.protocol_implementation
    impl
    state
    wire_message
    local_event
    local_output)
  =
{
  pe_config:
    Type0;

  pe_frame:
    Type0;

  pe_frame_ready:
    impl ->
    pe_config ->
    pe_frame ->
    state ->
    slprop;

  pe_io_ready:
    impl ->
    TCP.channel ->
    pe_frame ->
    TCP.bytes ->
    TCP.bytes ->
    state ->
    slprop;

  pe_action_frame:
    impl ->
    pe_config ->
    pe_frame ->
    state ->
    endpoint_action
      protocol.CPI.pi_network_frame
      local_event
      protocol.CPI.pi_local_frame ->
    slprop;

  pe_network_continuation:
    impl ->
    pe_config ->
    pe_frame ->
    state ->
    protocol.CPI.pi_network_frame ->
    slprop;

  pe_local_continuation:
    impl ->
    pe_config ->
    pe_frame ->
    state ->
    local_event ->
    protocol.CPI.pi_local_frame ->
    slprop;

  pe_next_action:
    i:impl ->
    cfg:pe_config ->
    frame:pe_frame ->
    received:Ghost.erased TCP.bytes ->
    sent:Ghost.erased TCP.bytes ->
    st:Ghost.erased state ->
      stt (endpoint_action
        protocol.CPI.pi_network_frame
        local_event
        protocol.CPI.pi_local_frame)
        (protocol.CPI.pi_invariant
           i
           (Ghost.reveal received)
           (Ghost.reveal sent)
           (Ghost.reveal st) **
         pe_frame_ready
           i
           cfg
           frame
           (Ghost.reveal st))
        (fun action ->
          protocol.CPI.pi_invariant
            i
            (Ghost.reveal received)
            (Ghost.reveal sent)
            (Ghost.reveal st) **
          pe_action_frame
            i
            cfg
            frame
            (Ghost.reveal st)
            action **
          pure (action_not_internal protocol action));

  pe_cancel_action:
    i:impl ->
    cfg:pe_config ->
    frame:pe_frame ->
    st:Ghost.erased state ->
    action:endpoint_action
      protocol.CPI.pi_network_frame
      local_event
      protocol.CPI.pi_local_frame ->
      stt unit
        (pe_action_frame
          i
          cfg
          frame
          (Ghost.reveal st)
          action)
        (fun _ ->
          pe_frame_ready
            i
            cfg
            frame
            (Ghost.reveal st));

  pe_finish_network_action:
    i:impl ->
    cfg:pe_config ->
    frame:pe_frame ->
    network_frame:protocol.CPI.pi_network_frame ->
    result:CPI.process_result ->
    input_contents:Ghost.erased TCP.bytes ->
    input_len:SZ.t ->
    old_out:Ghost.erased TCP.bytes ->
    out_contents:Ghost.erased TCP.bytes ->
    st0:Ghost.erased state ->
    st1:Ghost.erased state ->
    consumed:Ghost.erased TCP.bytes ->
    wire_outputs:Ghost.erased (list wire_message) ->
    local_outputs:Ghost.erased (list local_output) ->
      stt unit
        (pe_network_continuation
          i
          cfg
          frame
          (Ghost.reveal st0)
          network_frame **
         protocol.CPI.pi_network_frame_post
          network_frame
          result
          (Ghost.reveal input_contents)
          input_len
          (Ghost.reveal old_out)
          (Ghost.reveal out_contents)
          (Ghost.reveal st0)
          (Ghost.reveal st1)
          (Ghost.reveal consumed)
          (Ghost.reveal wire_outputs)
          (Ghost.reveal local_outputs))
        (fun _ ->
          pe_frame_ready
            i
            cfg
            frame
            (Ghost.reveal st1));

  pe_finish_local_action:
    i:impl ->
    cfg:pe_config ->
    frame:pe_frame ->
    ev:local_event ->
    local_frame:protocol.CPI.pi_local_frame ->
    result:CPI.process_result ->
    old_out:Ghost.erased TCP.bytes ->
    out_contents:Ghost.erased TCP.bytes ->
    st0:Ghost.erased state ->
    st1:Ghost.erased state ->
    wire_outputs:Ghost.erased (list wire_message) ->
    local_outputs:Ghost.erased (list local_output) ->
      stt unit
        (pe_local_continuation
          i
          cfg
          frame
          (Ghost.reveal st0)
          ev
          local_frame **
         protocol.CPI.pi_local_frame_post
          ev
          local_frame
          result
          (Ghost.reveal old_out)
          (Ghost.reveal out_contents)
          (Ghost.reveal st0)
          (Ghost.reveal st1)
          (Ghost.reveal wire_outputs)
          (Ghost.reveal local_outputs))
        (fun _ ->
          pe_frame_ready
            i
            cfg
            frame
            (Ghost.reveal st1));

  pe_network_io:
    Type0;

  pe_network_io_continuation:
    impl ->
    TCP.channel ->
    pe_frame ->
    TCP.bytes ->
    TCP.bytes ->
    state ->
    pe_network_io ->
    slprop;

  pe_network_input:
    pe_network_io ->
    array U8.t;

  pe_network_input_len:
    pe_network_io ->
    SZ.t;

  pe_network_output:
    pe_network_io ->
    array U8.t;

  pe_network_output_len:
    pe_network_io ->
    SZ.t;

  pe_network_input_contents:
    pe_network_io ->
    Ghost.erased TCP.bytes;

  pe_network_old_output:
    pe_network_io ->
    Ghost.erased TCP.bytes;

  pe_prepare_network:
    i:impl ->
    cfg:pe_config ->
    frame:pe_frame ->
    ch:TCP.channel ->
    network_frame:protocol.CPI.pi_network_frame ->
    received:Ghost.erased TCP.bytes ->
    sent:Ghost.erased TCP.bytes ->
    st:Ghost.erased state ->
      stt pe_network_io
        (pe_action_frame
          i
          cfg
          frame
          (Ghost.reveal st)
          (EndpointNeedInput network_frame) **
         pe_io_ready
         i
         ch
         frame
         (Ghost.reveal received)
         (Ghost.reveal sent)
         (Ghost.reveal st))
        (fun nio ->
         pe_network_io_continuation
           i
           ch
           frame
           (Ghost.reveal received)
           (Ghost.reveal sent)
           (Ghost.reveal st)
           nio **
         network_buffers
           (pe_network_input nio)
           (pe_network_input_len nio)
           (pe_network_output nio)
           (pe_network_output_len nio)
           (Ghost.reveal (pe_network_input_contents nio))
           (Ghost.reveal (pe_network_old_output nio)) **
         protocol.CPI.pi_network_frame_pre
           network_frame
           (pe_network_input nio)
            (pe_network_input_len nio)
            (pe_network_output nio)
            (pe_network_output_len nio)
            (Ghost.reveal (pe_network_input_contents nio))
            (Ghost.reveal (pe_network_old_output nio)) **
          pe_network_continuation
            i
            cfg
            frame
            (Ghost.reveal st)
            network_frame **
          pure (
            CPI.buffers_wf
              (Ghost.reveal (pe_network_input_contents nio))
              (pe_network_input_len nio)
              (Ghost.reveal (pe_network_old_output nio))
              (pe_network_output_len nio)));

  pe_finish_network_io:
    i:impl ->
    ch:TCP.channel ->
    frame:pe_frame ->
    nio:pe_network_io ->
    result:CPI.process_result ->
    received0:Ghost.erased TCP.bytes ->
    sent0:Ghost.erased TCP.bytes ->
    st0:Ghost.erased state ->
    received1:Ghost.erased TCP.bytes ->
    sent1:Ghost.erased TCP.bytes ->
    st1:Ghost.erased state ->
    out_contents:Ghost.erased TCP.bytes ->
    consumed:Ghost.erased TCP.bytes ->
    wire_outputs:Ghost.erased (list wire_message) ->
    local_outputs:Ghost.erased (list local_output) ->
      stt unit
        (pe_network_io_continuation
          i
          ch
          frame
          (Ghost.reveal received0)
          (Ghost.reveal sent0)
          (Ghost.reveal st0)
          nio **
         pts_to
          (pe_network_input nio)
          (Ghost.reveal (pe_network_input_contents nio)) **
         pts_to
          (pe_network_output nio)
          (Ghost.reveal out_contents) **
         pure (
          CPI.network_process_correct
            (protocol.CPI.pi_system i)
            (Ghost.reveal (pe_network_input_contents nio))
            (pe_network_input_len nio)
            (Ghost.reveal (pe_network_old_output nio))
            (Ghost.reveal out_contents)
            (pe_network_output_len nio)
            (Ghost.reveal received0)
            (Ghost.reveal sent0)
            (Ghost.reveal st0)
            result
            (Ghost.reveal received1)
            (Ghost.reveal sent1)
            (Ghost.reveal st1)
            (Ghost.reveal consumed)
            (Ghost.reveal wire_outputs)
            (Ghost.reveal local_outputs)))
        (fun _ ->
          pe_io_ready
            i
            ch
            frame
            (Ghost.reveal received1)
            (Ghost.reveal sent1)
            (Ghost.reveal st1));

  pe_local_io:
    Type0;

  pe_local_io_continuation:
    impl ->
    TCP.channel ->
    pe_frame ->
    TCP.bytes ->
    TCP.bytes ->
    state ->
    local_event ->
    pe_local_io ->
    slprop;

  pe_local_output:
    pe_local_io ->
    array U8.t;

  pe_local_output_len:
    pe_local_io ->
    SZ.t;

  pe_local_old_output:
    pe_local_io ->
    Ghost.erased TCP.bytes;

  pe_prepare_local:
    i:impl ->
    cfg:pe_config ->
    frame:pe_frame ->
    ch:TCP.channel ->
    ev:local_event ->
    local_frame:protocol.CPI.pi_local_frame ->
    received:Ghost.erased TCP.bytes ->
    sent:Ghost.erased TCP.bytes ->
    st:Ghost.erased state ->
      stt pe_local_io
        (pe_action_frame
          i
          cfg
          frame
          (Ghost.reveal st)
          (EndpointLocal ev local_frame) **
         pe_io_ready
          i
          ch
          frame
          (Ghost.reveal received)
          (Ghost.reveal sent)
          (Ghost.reveal st))
        (fun lio ->
          pe_local_io_continuation
            i
            ch
            frame
            (Ghost.reveal received)
            (Ghost.reveal sent)
            (Ghost.reveal st)
            ev
            lio **
          local_output_buffer
            (pe_local_output lio)
            (pe_local_output_len lio)
            (Ghost.reveal (pe_local_old_output lio)) **
          protocol.CPI.pi_local_frame_pre
            ev
            local_frame
            (Ghost.reveal st)
            (pe_local_output lio)
            (pe_local_output_len lio)
            (Ghost.reveal (pe_local_old_output lio)) **
          pe_local_continuation
            i
            cfg
            frame
            (Ghost.reveal st)
            ev
            local_frame);

  pe_finish_local_io:
    i:impl ->
    ch:TCP.channel ->
    frame:pe_frame ->
    lio:pe_local_io ->
    ev:local_event ->
    result:CPI.process_result ->
    received0:Ghost.erased TCP.bytes ->
    sent0:Ghost.erased TCP.bytes ->
    st0:Ghost.erased state ->
    received1:Ghost.erased TCP.bytes ->
    sent1:Ghost.erased TCP.bytes ->
    st1:Ghost.erased state ->
    out_contents:Ghost.erased TCP.bytes ->
    wire_outputs:Ghost.erased (list wire_message) ->
    local_outputs:Ghost.erased (list local_output) ->
      stt unit
        (pe_local_io_continuation
          i
          ch
          frame
          (Ghost.reveal received0)
          (Ghost.reveal sent0)
          (Ghost.reveal st0)
          ev
          lio **
         pts_to
          (pe_local_output lio)
          (Ghost.reveal out_contents) **
         pure (
          CPI.local_process_correct
            (protocol.CPI.pi_system i)
            ev
            (Ghost.reveal (pe_local_old_output lio))
            (Ghost.reveal out_contents)
            (pe_local_output_len lio)
            (Ghost.reveal received0)
            (Ghost.reveal sent0)
            (Ghost.reveal st0)
            result
            (Ghost.reveal received1)
            (Ghost.reveal sent1)
            (Ghost.reveal st1)
            (Ghost.reveal wire_outputs)
            (Ghost.reveal local_outputs)))
        (fun _ ->
          pe_io_ready
            i
            ch
            frame
            (Ghost.reveal received1)
            (Ghost.reveal sent1)
            (Ghost.reveal st1));
}
