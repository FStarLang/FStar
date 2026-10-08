module Pulse.Lib.Protocol.ChannelImplementation

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module CPI = Pulse.Lib.Protocol.Implementation
module ID = FStar.IndefiniteDescription
module L = FStar.List.Tot
module Pre = FStar.Preorder
module RTC = FStar.ReflexiveTransitiveClosure
module Seq = FStar.Seq
module SZ = FStar.SizeT
module TCP = Pulse.Lib.TCP
module U8 = FStar.UInt8
module WFSM = Pulse.Lib.Protocol.WireFormatStateMachine

noeq
type application_log (message:Type0) = {
  sent: list message;
  received: list message;
}

let empty_application_log (#message:Type0) : application_log message = {
  sent = [];
  received = [];
}

let append_sent
  (#message:Type0)
  (log:application_log message)
  (msg:message)
  : application_log message =
  { log with sent = L.append log.sent [msg] }

let append_received
  (#message:Type0)
  (log:application_log message)
  (msg:message)
  : application_log message =
  { log with received = L.append log.received [msg] }

let application_log_extends
  (#message:Type0)
  (old_log:application_log message)
  (new_log:application_log message)
  : prop =
  exists sent_delta received_delta.
    new_log.sent == L.append old_log.sent sent_delta /\
    new_log.received == L.append old_log.received received_delta

let exact_io_history_matches
  (wire_received wire_sent io_received io_sent:TCP.bytes)
  : prop =
  Seq.equal io_received wire_received /\
  Seq.equal io_sent wire_sent

(**
  Snapshots track the complete transport history.  The closure is used only as
  the monotonic-reference preorder; [lemma_io_history_preorder_extends]
  recovers the concrete prefix relation needed by the public channel law.
**)
let io_history_preorder : Pre.preorder TCP.history =
  RTC.closure TCP.history_extends

let lemma_io_history_preorder_of_extends
  (old_history new_history:TCP.history)
  : Lemma
      (requires TCP.history_extends old_history new_history)
      (ensures io_history_preorder old_history new_history)
=
  RTC.closure_step TCP.history_extends old_history new_history

let lemma_io_history_preorder_extends
  (old_history new_history:TCP.history)
  : Lemma
      (requires io_history_preorder old_history new_history)
      (ensures TCP.history_extends old_history new_history)
=
  RTC.induct
    TCP.history_extends
    TCP.history_extends
    (fun history ->
      CPI.lemma_bytes_extends_refl history.TCP.tcp_received;
      CPI.lemma_bytes_extends_refl history.TCP.tcp_sent)
    (fun old_history new_history -> ())
    (fun old_history middle_history new_history ->
      CPI.lemma_bytes_extends_trans
        old_history.TCP.tcp_received
        middle_history.TCP.tcp_received
        new_history.TCP.tcp_received;
      CPI.lemma_bytes_extends_trans
        old_history.TCP.tcp_sent
        middle_history.TCP.tcp_sent
        new_history.TCP.tcp_sent)
    old_history
    new_history
    ()

let channel_state_valid
  (#impl #protocol_impl #state #wire_message #local_event #local_output #message:Type0)
  (protocol:CPI.protocol_implementation
    protocol_impl
    state
    wire_message
    local_event
    local_output)
  (protocol_impl_of:impl -> GTot protocol_impl)
  (project:state -> GTot (application_log message))
  (i:impl)
  (wire_received:TCP.bytes)
  (wire_sent:TCP.bytes)
  (pending:TCP.bytes)
  (app_log:application_log message)
  : prop =
  // Every received transport byte is either protocol-consumed or still pending.
  exists st consumed_received.
    Seq.equal
      wire_received
      (Seq.append consumed_received pending) /\
    WFSM.valid_byte_trace
      (protocol.CPI.pi_system (protocol_impl_of i))
      consumed_received
      st
      wire_sent
      Seq.empty /\
    app_log == project st

let channel_snapshot_ahead
  (#impl #protocol_impl #state #wire_message #local_event #local_output #message:Type0)
  (protocol:CPI.protocol_implementation
    protocol_impl
    state
    wire_message
    local_event
    local_output)
  (protocol_impl_of:impl -> GTot protocol_impl)
  (project:state -> GTot (application_log message))
  (i:impl)
  (old_received:TCP.bytes)
  (old_sent:TCP.bytes)
  (old_log:application_log message)
  (new_received:TCP.bytes)
  (new_sent:TCP.bytes)
  (new_log:application_log message)
  : prop =
  CPI.histories_ahead old_received old_sent new_received new_sent /\
  application_log_extends old_log new_log /\
  exists old_state new_state.
    old_log == project old_state /\
    new_log == project new_state /\
    CPI.state_ahead
      (protocol.CPI.pi_system (protocol_impl_of i))
      old_state
      new_state

let send_transition
  (#message #send_status:Type0)
  (message_of_bytes:TCP.bytes -> GTot message)
  (succeeded:send_status -> GTot bool)
  (status:send_status)
  (payload:TCP.bytes)
  (old_received:TCP.bytes)
  (old_sent:TCP.bytes)
  (old_log:application_log message)
  (new_received:TCP.bytes)
  (new_sent:TCP.bytes)
  (new_log:application_log message)
  : prop =
  CPI.histories_ahead old_received old_sent new_received new_sent /\
  new_log ==
    (if succeeded status
     then append_sent old_log (message_of_bytes payload)
     else old_log)

let receive_transition
  (#message #receive_result:Type0)
  (message_of_bytes:TCP.bytes -> GTot message)
  (succeeded:receive_result -> GTot bool)
  (result_length:receive_result -> GTot SZ.t)
  (result:receive_result)
  (output:TCP.bytes)
  (old_received:TCP.bytes)
  (old_sent:TCP.bytes)
  (old_log:application_log message)
  (new_received:TCP.bytes)
  (new_sent:TCP.bytes)
  (new_log:application_log message)
  : prop =
  CPI.histories_ahead old_received old_sent new_received new_sent /\
  new_log ==
    (if succeeded result
     then
       append_received
         old_log
         (message_of_bytes
           (if SZ.v (result_length result) <= Seq.length output
            then Seq.slice output 0 (SZ.v (result_length result))
            else Seq.empty))
     else old_log)

noextract
class channel_implementation
  (impl:Type0)
  (protocol_impl:Type0)
  (state:Type0)
  (wire_message:Type0)
  (local_event:Type0)
  (local_output:Type0)
  (message:Type0)
  (send_status:Type0)
  (receive_result:Type0)
  (protocol:CPI.protocol_implementation
    protocol_impl
    state
    wire_message
    local_event
    local_output)
  =
{
  ci_protocol_impl:
    impl -> GTot protocol_impl;

  ci_project:
    state -> GTot (application_log message);

  ci_message_of_bytes:
    TCP.bytes -> GTot message;

  ci_channel_inv:
    impl ->
    TCP.bytes ->
    TCP.bytes ->
    TCP.bytes ->
    application_log message ->
    slprop;

  // Terminal ownership remains exact but makes no protocol-validity claim.
  ci_terminal_inv:
    impl ->
    TCP.bytes ->
    TCP.bytes ->
    application_log message ->
    slprop;

  ci_io_frame:
    impl ->
    TCP.channel ->
    TCP.bytes ->
    TCP.bytes ->
    TCP.bytes ->
    application_log message ->
    slprop;

  ci_snapshot:
    impl ->
    TCP.bytes ->
    TCP.bytes ->
    application_log message ->
    slprop;

  ci_send_succeeded:
    send_status -> GTot bool;

  ci_send_usable:
    send_status -> GTot bool;

  ci_receive_succeeded:
    receive_result -> GTot bool;

  ci_receive_usable:
    receive_result -> GTot bool;

  ci_receive_length:
    receive_result -> GTot SZ.t;

  ci_open_io_channel:
    i:impl ->
    wire_received:Ghost.erased TCP.bytes ->
    wire_sent:Ghost.erased TCP.bytes ->
    pending:Ghost.erased TCP.bytes ->
    app_log:Ghost.erased (application_log message) ->
      stt_ghost TCP.channel emp_inames
        (ci_channel_inv
          i
          (Ghost.reveal wire_received)
          (Ghost.reveal wire_sent)
          (Ghost.reveal pending)
          (Ghost.reveal app_log))
        (fun ch ->
          TCP.is_channel
            ch
            (Ghost.reveal wire_received)
            (Ghost.reveal wire_sent) **
          ci_io_frame
            i
            ch
            (Ghost.reveal wire_received)
            (Ghost.reveal wire_sent)
            (Ghost.reveal pending)
            (Ghost.reveal app_log));

  ci_close_io_channel:
    i:impl ->
    ch:TCP.channel ->
    wire_received:Ghost.erased TCP.bytes ->
    wire_sent:Ghost.erased TCP.bytes ->
    pending:Ghost.erased TCP.bytes ->
    app_log:Ghost.erased (application_log message) ->
      stt_ghost unit emp_inames
        (TCP.is_channel
          ch
          (Ghost.reveal wire_received)
          (Ghost.reveal wire_sent) **
         ci_io_frame
          i
          ch
          (Ghost.reveal wire_received)
          (Ghost.reveal wire_sent)
          (Ghost.reveal pending)
          (Ghost.reveal app_log))
        (fun _ ->
          ci_channel_inv
            i
            (Ghost.reveal wire_received)
            (Ghost.reveal wire_sent)
            (Ghost.reveal pending)
            (Ghost.reveal app_log));

  ci_invariant_valid:
    i:impl ->
    wire_received:Ghost.erased TCP.bytes ->
    wire_sent:Ghost.erased TCP.bytes ->
    pending:Ghost.erased TCP.bytes ->
    app_log:Ghost.erased (application_log message) ->
      stt_ghost unit emp_inames
        (ci_channel_inv
          i
          (Ghost.reveal wire_received)
          (Ghost.reveal wire_sent)
          (Ghost.reveal pending)
          (Ghost.reveal app_log))
        (fun _ ->
          ci_channel_inv
            i
            (Ghost.reveal wire_received)
            (Ghost.reveal wire_sent)
            (Ghost.reveal pending)
            (Ghost.reveal app_log) **
          pure (
            channel_state_valid
              protocol
              ci_protocol_impl
              ci_project
              i
              (Ghost.reveal wire_received)
              (Ghost.reveal wire_sent)
              (Ghost.reveal pending)
              (Ghost.reveal app_log)));

  ci_take_snapshot:
    i:impl ->
    wire_received:Ghost.erased TCP.bytes ->
    wire_sent:Ghost.erased TCP.bytes ->
    pending:Ghost.erased TCP.bytes ->
    app_log:Ghost.erased (application_log message) ->
      stt_ghost unit emp_inames
        (ci_channel_inv
          i
          (Ghost.reveal wire_received)
          (Ghost.reveal wire_sent)
          (Ghost.reveal pending)
          (Ghost.reveal app_log))
        (fun _ ->
          ci_channel_inv
            i
            (Ghost.reveal wire_received)
            (Ghost.reveal wire_sent)
            (Ghost.reveal pending)
            (Ghost.reveal app_log) **
          ci_snapshot
            i
            (Ghost.reveal wire_received)
            (Ghost.reveal wire_sent)
            (Ghost.reveal app_log));

  ci_recall_snapshot:
    i:impl ->
    old_received:Ghost.erased TCP.bytes ->
    old_sent:Ghost.erased TCP.bytes ->
    old_log:Ghost.erased (application_log message) ->
    new_received:Ghost.erased TCP.bytes ->
    new_sent:Ghost.erased TCP.bytes ->
    new_pending:Ghost.erased TCP.bytes ->
    new_log:Ghost.erased (application_log message) ->
      stt_ghost unit emp_inames
        (ci_snapshot
          i
          (Ghost.reveal old_received)
          (Ghost.reveal old_sent)
          (Ghost.reveal old_log) **
         ci_channel_inv
          i
          (Ghost.reveal new_received)
          (Ghost.reveal new_sent)
          (Ghost.reveal new_pending)
          (Ghost.reveal new_log))
        (fun _ ->
          ci_snapshot
            i
            (Ghost.reveal old_received)
            (Ghost.reveal old_sent)
            (Ghost.reveal old_log) **
          ci_channel_inv
            i
            (Ghost.reveal new_received)
            (Ghost.reveal new_sent)
            (Ghost.reveal new_pending)
            (Ghost.reveal new_log) **
          pure (
            channel_snapshot_ahead
              protocol
              ci_protocol_impl
              ci_project
              i
              (Ghost.reveal old_received)
              (Ghost.reveal old_sent)
              (Ghost.reveal old_log)
              (Ghost.reveal new_received)
              (Ghost.reveal new_sent)
              (Ghost.reveal new_log)));

  ci_send:
    i:impl ->
    wire_received0:Ghost.erased TCP.bytes ->
    wire_sent0:Ghost.erased TCP.bytes ->
    pending0:Ghost.erased TCP.bytes ->
    app_log0:Ghost.erased (application_log message) ->
    payload:array U8.t ->
    payload_bytes:Ghost.erased TCP.bytes ->
    payload_len:SZ.t ->
      stt send_status
        (ci_channel_inv
           i
           (Ghost.reveal wire_received0)
           (Ghost.reveal wire_sent0)
           (Ghost.reveal pending0)
           (Ghost.reveal app_log0) **
         pts_to payload (Ghost.reveal payload_bytes) **
         pure (Seq.length (Ghost.reveal payload_bytes) == SZ.v payload_len))
        (fun status ->
          exists* wire_received1 wire_sent1 pending1 app_log1.
            (if ci_send_usable status
             then
               ci_channel_inv
                 i wire_received1 wire_sent1 pending1 app_log1
             else
               ci_terminal_inv
                 i wire_received1 wire_sent1 app_log1) **
            pts_to payload (Ghost.reveal payload_bytes) **
            pure (
              send_transition
                ci_message_of_bytes
                ci_send_succeeded
                status
                (Ghost.reveal payload_bytes)
                (Ghost.reveal wire_received0)
                (Ghost.reveal wire_sent0)
                (Ghost.reveal app_log0)
                wire_received1
                wire_sent1
                app_log1));

  ci_receive:
    i:impl ->
    wire_received0:Ghost.erased TCP.bytes ->
    wire_sent0:Ghost.erased TCP.bytes ->
    pending0:Ghost.erased TCP.bytes ->
    app_log0:Ghost.erased (application_log message) ->
    out:array U8.t ->
    old_output:Ghost.erased TCP.bytes ->
    out_len:SZ.t ->
    local_fuel:SZ.t ->
    network_fuel:SZ.t ->
      stt receive_result
        (ci_channel_inv
           i
           (Ghost.reveal wire_received0)
           (Ghost.reveal wire_sent0)
           (Ghost.reveal pending0)
           (Ghost.reveal app_log0) **
         pts_to out (Ghost.reveal old_output) **
         pure (Seq.length (Ghost.reveal old_output) == SZ.v out_len))
        (fun result ->
          exists* wire_received1 wire_sent1 pending1 app_log1 output.
            (if ci_receive_usable result
             then
               ci_channel_inv
                 i wire_received1 wire_sent1 pending1 app_log1
             else
               ci_terminal_inv
                 i wire_received1 wire_sent1 app_log1) **
            pts_to out output **
            pure (
              Seq.length output == SZ.v out_len /\
              SZ.v (ci_receive_length result) <= SZ.v out_len /\
              receive_transition
                ci_message_of_bytes
                ci_receive_succeeded
                ci_receive_length
                result
                output
                (Ghost.reveal wire_received0)
                (Ghost.reveal wire_sent0)
                (Ghost.reveal app_log0)
                wire_received1
                wire_sent1
                app_log1));
}
