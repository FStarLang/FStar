module Pulse.Lib.Protocol.Driver

#lang-pulse

open Pulse.Lib.Pervasives

module CPI = Pulse.Lib.Protocol.Implementation
module PE = Pulse.Lib.Protocol.Endpoint
module SZ = FStar.SizeT
module TCP = Pulse.Lib.TCP

// Generic fuel-bounded driver over a ProtocolEndpoint and a Pulse.Lib.TCP channel.
//
// The endpoint owns the concrete frame and I/O buffer discipline, while this
// module owns the scheduling structure: ask for the next action, run the
// corresponding network/local handler, finish endpoint action resources, finish
// TCP/output resources, and iterate until done, failure, or fuel exhaustion.
// Extraction-facing code can specialize this proof-generic loop monomorphically
// for a concrete endpoint, as the calc example (share/pulse/examples/protocol) does.
type driver_status =
  | DriverNetworkStep
  | DriverLocalStep
  | DriverDone
  | DriverFailed

noeq
type driver_result = {
  driver_status: driver_status;
  driver_process_result: option CPI.process_result;
}

type driver_run_status =
  | DriverRunDone
  | DriverRunFailed
  | DriverRunFuelExhausted

noeq
type driver_run_result = {
  driver_run_status: driver_run_status;
  driver_run_last_step: option CPI.process_result;
}

let network_driver_status
  (result:CPI.process_result)
  : Tot (status:driver_status { status == DriverNetworkStep \/ status == DriverFailed }) =
  match result.CPI.process_status with
  | CPI.StepOk
  | CPI.NeedMoreInput -> DriverNetworkStep
  | CPI.ParseFailed
  | CPI.DecodeError
  | CPI.IllegalTransition
  | CPI.OutputBufferTooSmall
  | CPI.ConnectionFailed -> DriverFailed

let local_driver_status
  (result:CPI.process_result)
  : Tot (status:driver_status { status == DriverLocalStep \/ status == DriverFailed }) =
  match result.CPI.process_status with
  | CPI.StepOk -> DriverLocalStep
  | CPI.NeedMoreInput
  | CPI.ParseFailed
  | CPI.DecodeError
  | CPI.IllegalTransition
  | CPI.OutputBufferTooSmall
  | CPI.ConnectionFailed -> DriverFailed

noextract
fn drive_once
  #impl #state #wire_message #local_event #local_output
  (#protocol:CPI.protocol_implementation
    impl
    state
    wire_message
    local_event
    local_output)
  (#endpoint:PE.protocol_endpoint
    impl
    state
    wire_message
    local_event
    local_output
    protocol)
  (i:impl)
  (cfg:endpoint.PE.pe_config)
  (frame:endpoint.PE.pe_frame)
  (ch:TCP.channel)
  (received:Ghost.erased TCP.bytes)
  (sent:Ghost.erased TCP.bytes)
  (st:Ghost.erased state)
requires
  protocol.CPI.pi_invariant
    i
    (Ghost.reveal received)
    (Ghost.reveal sent)
    (Ghost.reveal st) **
  endpoint.PE.pe_frame_ready
    i
    cfg
    frame
    (Ghost.reveal st) **
  endpoint.PE.pe_io_ready
    i
    ch
    frame
    (Ghost.reveal received)
    (Ghost.reveal sent)
    (Ghost.reveal st)
returns result:driver_result
ensures
  (match result.driver_status with
  | DriverNetworkStep
  | DriverLocalStep
  | DriverFailed ->
    exists* (received1:Ghost.erased TCP.bytes)
            (sent1:Ghost.erased TCP.bytes)
            (st1:Ghost.erased state).
      protocol.CPI.pi_invariant
        i
        (Ghost.reveal received1)
        (Ghost.reveal sent1)
        (Ghost.reveal st1) **
      endpoint.PE.pe_frame_ready
        i
        cfg
        frame
        (Ghost.reveal st1) **
      endpoint.PE.pe_io_ready
        i
        ch
        frame
        (Ghost.reveal received1)
        (Ghost.reveal sent1)
        (Ghost.reveal st1)
  | DriverDone ->
      protocol.CPI.pi_invariant
        i
        (Ghost.reveal received)
        (Ghost.reveal sent)
        (Ghost.reveal st) **
      endpoint.PE.pe_frame_ready
        i
        cfg
        frame
        (Ghost.reveal st) **
      endpoint.PE.pe_io_ready
        i
        ch
        frame
        (Ghost.reveal received)
        (Ghost.reveal sent)
        (Ghost.reveal st))
{
  let next_action = endpoint.PE.pe_next_action;
  let action =
    next_action
      i
      cfg
      frame
      received
      sent
      st;
  match action {
    PE.EndpointNeedInput network_frame -> {
      let prepare_network = endpoint.PE.pe_prepare_network;
      let nio =
        prepare_network
        i
        cfg
        frame
        ch
        network_frame
        received
        sent
        st;
      let process_network = protocol.CPI.pi_process_network;
      let process_result =
        process_network
          i
          network_frame
          (endpoint.PE.pe_network_input nio)
          (endpoint.PE.pe_network_input_len nio)
          (endpoint.PE.pe_network_output nio)
          (endpoint.PE.pe_network_output_len nio)
          received
          sent
          st
          (endpoint.PE.pe_network_input_contents nio)
          (endpoint.PE.pe_network_old_output nio);
      with received1 sent1 st1 out_contents consumed wire_outputs local_outputs.
      assert (
        protocol.CPI.pi_invariant
          i
          (Ghost.reveal received1)
          (Ghost.reveal sent1)
          (Ghost.reveal st1) **
        protocol.CPI.pi_network_frame_post
          network_frame
          process_result
          (Ghost.reveal (endpoint.PE.pe_network_input_contents nio))
          (endpoint.PE.pe_network_input_len nio)
          (Ghost.reveal (endpoint.PE.pe_network_old_output nio))
          out_contents
          (Ghost.reveal st)
          (Ghost.reveal st1)
          consumed
          wire_outputs
          local_outputs);
      let out_contentse = Ghost.hide out_contents;
      let consumede = Ghost.hide consumed;
      let wire_outputse = Ghost.hide wire_outputs;
      let local_outputse = Ghost.hide local_outputs;
      let finish_network_action = endpoint.PE.pe_finish_network_action;
      assert (pure ((Ghost.reveal out_contentse) == out_contents));
      assert (pure ((Ghost.reveal consumede) == consumed));
      assert (pure ((Ghost.reveal wire_outputse) == wire_outputs));
      assert (pure ((Ghost.reveal local_outputse) == local_outputs));
      rewrite
        (protocol.CPI.pi_network_frame_post
          network_frame
          process_result
          (Ghost.reveal (endpoint.PE.pe_network_input_contents nio))
          (endpoint.PE.pe_network_input_len nio)
          (Ghost.reveal (endpoint.PE.pe_network_old_output nio))
          out_contents
          (Ghost.reveal st)
          (Ghost.reveal st1)
          consumed
          wire_outputs
          local_outputs)
        as
        (protocol.CPI.pi_network_frame_post
          network_frame
          process_result
          (Ghost.reveal (endpoint.PE.pe_network_input_contents nio))
          (endpoint.PE.pe_network_input_len nio)
          (Ghost.reveal (endpoint.PE.pe_network_old_output nio))
          (Ghost.reveal out_contentse)
          (Ghost.reveal st)
          (Ghost.reveal st1)
          (Ghost.reveal consumede)
          (Ghost.reveal wire_outputse)
          (Ghost.reveal local_outputse));
      finish_network_action
        i
        cfg
        frame
        network_frame
        process_result
        (endpoint.PE.pe_network_input_contents nio)
        (endpoint.PE.pe_network_input_len nio)
        (endpoint.PE.pe_network_old_output nio)
        out_contentse
        st
        st1
        consumede
        wire_outputse
        local_outputse;
      let finish_network_io = endpoint.PE.pe_finish_network_io;
      finish_network_io
        i
        ch
        frame
        nio
        process_result
        received
        sent
        st
        received1
        sent1
        st1
        out_contentse
        consumede
        wire_outputse
        local_outputse;
      let status = network_driver_status process_result;
      assert (pure (status == DriverNetworkStep \/ status == DriverFailed));
      match status {
        DriverNetworkStep -> {
          ({
            driver_status = DriverNetworkStep;
            driver_process_result = Some process_result;
          })
        }
        DriverFailed -> {
          ({
            driver_status = DriverFailed;
            driver_process_result = Some process_result;
          })
        }
        DriverLocalStep -> {
          ({
            driver_status = DriverFailed;
            driver_process_result = Some process_result;
          })
        }
        DriverDone -> {
          ({
            driver_status = DriverFailed;
            driver_process_result = Some process_result;
          })
        }
      }
    }
    PE.EndpointLocal ev local_frame -> {
      let prepare_local = endpoint.PE.pe_prepare_local;
      let lio =
        prepare_local
        i
        cfg
        frame
        ch
        ev
        local_frame
        received
        sent
        st;
      let process_local = protocol.CPI.pi_process_local;
      let process_result =
        process_local
          i
          ev
          local_frame
          (endpoint.PE.pe_local_output lio)
          (endpoint.PE.pe_local_output_len lio)
          received
          sent
          st
          (endpoint.PE.pe_local_old_output lio);
      with received1 sent1 st1 out_contents wire_outputs local_outputs.
      assert (
        protocol.CPI.pi_invariant
          i
          (Ghost.reveal received1)
          (Ghost.reveal sent1)
          (Ghost.reveal st1) **
        protocol.CPI.pi_local_frame_post
          ev
          local_frame
          process_result
          (Ghost.reveal (endpoint.PE.pe_local_old_output lio))
          out_contents
          (Ghost.reveal st)
          (Ghost.reveal st1)
          wire_outputs
          local_outputs);
      let out_contentse = Ghost.hide out_contents;
      let wire_outputse = Ghost.hide wire_outputs;
      let local_outputse = Ghost.hide local_outputs;
      let finish_local_action = endpoint.PE.pe_finish_local_action;
      assert (pure ((Ghost.reveal out_contentse) == out_contents));
      assert (pure ((Ghost.reveal wire_outputse) == wire_outputs));
      assert (pure ((Ghost.reveal local_outputse) == local_outputs));
      rewrite
        (protocol.CPI.pi_local_frame_post
          ev
          local_frame
          process_result
          (Ghost.reveal (endpoint.PE.pe_local_old_output lio))
          out_contents
          (Ghost.reveal st)
          (Ghost.reveal st1)
          wire_outputs
          local_outputs)
        as
        (protocol.CPI.pi_local_frame_post
          ev
          local_frame
          process_result
          (Ghost.reveal (endpoint.PE.pe_local_old_output lio))
          (Ghost.reveal out_contentse)
          (Ghost.reveal st)
          (Ghost.reveal st1)
          (Ghost.reveal wire_outputse)
          (Ghost.reveal local_outputse));
      finish_local_action
        i
        cfg
        frame
        ev
        local_frame
        process_result
        (endpoint.PE.pe_local_old_output lio)
        out_contentse
        st
        st1
        wire_outputse
        local_outputse;
      let finish_local_io = endpoint.PE.pe_finish_local_io;
      finish_local_io
        i
        ch
        frame
        lio
        ev
        process_result
        received
        sent
        st
        received1
        sent1
        st1
        out_contentse
        wire_outputse
        local_outputse;
      let status = local_driver_status process_result;
      assert (pure (status == DriverLocalStep \/ status == DriverFailed));
      match status {
        DriverLocalStep -> {
          ({
            driver_status = DriverLocalStep;
            driver_process_result = Some process_result;
          })
        }
        DriverFailed -> {
          ({
            driver_status = DriverFailed;
            driver_process_result = Some process_result;
          })
        }
        DriverNetworkStep -> {
          ({
            driver_status = DriverFailed;
            driver_process_result = Some process_result;
          })
        }
        DriverDone -> {
          ({
            driver_status = DriverFailed;
            driver_process_result = Some process_result;
          })
        }
      }
    }
    PE.EndpointDone -> {
      let cancel_action = endpoint.PE.pe_cancel_action;
      cancel_action i cfg frame st PE.EndpointDone;
      ({
        driver_status = DriverDone;
        driver_process_result = None;
      })
    }
    PE.EndpointFailed -> {
      let cancel_action = endpoint.PE.pe_cancel_action;
      cancel_action i cfg frame st PE.EndpointFailed;
      ({
        driver_status = DriverFailed;
        driver_process_result = None;
      })
    }
  }
}

noextract
fn rec drive_steps
    #impl #state #wire_message #local_event #local_output
    (#protocol:CPI.protocol_implementation
      impl
      state
      wire_message
      local_event
      local_output)
    (#endpoint:PE.protocol_endpoint
      impl
      state
      wire_message
      local_event
      local_output
      protocol)
    (i:impl)
    (cfg:endpoint.PE.pe_config)
    (frame:endpoint.PE.pe_frame)
    (ch:TCP.channel)
    (fuel:SZ.t)
    (received:Ghost.erased TCP.bytes)
    (sent:Ghost.erased TCP.bytes)
    (st:Ghost.erased state)
  requires
    protocol.CPI.pi_invariant
      i
      (Ghost.reveal received)
      (Ghost.reveal sent)
      (Ghost.reveal st) **
    endpoint.PE.pe_frame_ready
      i
      cfg
      frame
      (Ghost.reveal st) **
    endpoint.PE.pe_io_ready
      i
      ch
      frame
      (Ghost.reveal received)
      (Ghost.reveal sent)
      (Ghost.reveal st)
  returns result:driver_run_result
  ensures
    exists* (received1:Ghost.erased TCP.bytes)
            (sent1:Ghost.erased TCP.bytes)
            (st1:Ghost.erased state).
      protocol.CPI.pi_invariant
        i
        (Ghost.reveal received1)
        (Ghost.reveal sent1)
        (Ghost.reveal st1) **
      endpoint.PE.pe_frame_ready
        i
        cfg
        frame
        (Ghost.reveal st1) **
      endpoint.PE.pe_io_ready
        i
        ch
        frame
        (Ghost.reveal received1)
        (Ghost.reveal sent1)
        (Ghost.reveal st1)
  decreases (SZ.v fuel)
  {
    if (fuel = 0sz) {
      ({
        driver_run_status = DriverRunFuelExhausted;
        driver_run_last_step = None;
      })
    } else {
      assert (pure (0 < SZ.v fuel));
      let step = drive_once i cfg frame ch received sent st;
      match step.driver_status {
        DriverNetworkStep -> {
          with received1 sent1 st1.
            assert (
              protocol.CPI.pi_invariant
                i
                (Ghost.reveal received1)
                (Ghost.reveal sent1)
                (Ghost.reveal st1) **
              endpoint.PE.pe_frame_ready
                i
                cfg
                frame
                (Ghost.reveal st1) **
              endpoint.PE.pe_io_ready
                i
                ch
                frame
                (Ghost.reveal received1)
                (Ghost.reveal sent1)
                (Ghost.reveal st1));
          let next_fuel = SZ.sub fuel 1sz;
          assert (pure (SZ.v next_fuel < SZ.v fuel));
          drive_steps i cfg frame ch next_fuel received1 sent1 st1
        }
        DriverLocalStep -> {
          with received1 sent1 st1.
            assert (
              protocol.CPI.pi_invariant
                i
                (Ghost.reveal received1)
                (Ghost.reveal sent1)
                (Ghost.reveal st1) **
              endpoint.PE.pe_frame_ready
                i
                cfg
                frame
                (Ghost.reveal st1) **
              endpoint.PE.pe_io_ready
                i
                ch
                frame
                (Ghost.reveal received1)
                (Ghost.reveal sent1)
                (Ghost.reveal st1));
          let next_fuel = SZ.sub fuel 1sz;
          assert (pure (SZ.v next_fuel < SZ.v fuel));
          drive_steps i cfg frame ch next_fuel received1 sent1 st1
        }
        DriverDone -> {
          ({
            driver_run_status = DriverRunDone;
            driver_run_last_step = step.driver_process_result;
          })
        }
        DriverFailed -> {
          with received1 sent1 st1.
            assert (
              protocol.CPI.pi_invariant
                i
                (Ghost.reveal received1)
                (Ghost.reveal sent1)
                (Ghost.reveal st1) **
              endpoint.PE.pe_frame_ready
                i
                cfg
                frame
                (Ghost.reveal st1) **
              endpoint.PE.pe_io_ready
                i
                ch
                frame
                (Ghost.reveal received1)
                (Ghost.reveal sent1)
                (Ghost.reveal st1));
          ({
            driver_run_status = DriverRunFailed;
            driver_run_last_step = step.driver_process_result;
          })
        }
      }
    }
  }
