module Calc.Client.Protocol

(**
  Canonical `Pulse.Lib.Protocol.StateMachine` instance for the calculator *client*.

  This is the client-side mirror of `Calc.Protocol.calc_frame_state_machine`
  (the server's framework instance). Where the server's state machine `receives`
  requests as `WireEvent`s and `sends` responses as wire outputs, the client's
  state machine:

    - issues a request as an application-driven `LocalEvent`
      (`CalcClientIssue b`), emitting the request frame `b` as a wire output;
    - receives the server's response frame as a `WireEvent`, delivering it to the
      application as a local output.

  The client's abstract state is `Calc.Client.Log.client_state_abs` (the
  two-phase Idle/Awaiting machine over a predicted-server `calc_log`). We reuse
  the same wire format as the server (`Calc.Protocol.calc_frame_wire_format`):
  both requests and responses are 5-byte `calc_frame`s.

  The bridging lemma `lemma_client_single_step_evolves` connects the hand-rolled
  `client_single_step` relation (which the low-level `Calc.Client` operations
  establish) to `SM.state_evolves` of this framework instance, exactly mirroring
  `Calc.Server.CanonicalProtocol.lemma_calc_server_step_rel_state_ahead`.
**)

module L = FStar.List.Tot
module Seq = FStar.Seq
module SM = Pulse.Lib.Protocol.StateMachine
module WF = Pulse.Lib.Protocol.WireFormat
module WFSM = Pulse.Lib.Protocol.WireFormatStateMachine
module CalcP = Calc.Protocol

open Calc.Spec
open Calc.Wire
open Calc.Log
open Calc.Client.Log

(** A well-formed frame on the wire (same 5-byte `calc_frame` as the server). **)
type client_wire_message = CalcP.calc_frame

(** Application-driven local events: the application asks to issue a request. **)
type calc_client_local_event =
  | CalcClientIssue : CalcP.calc_frame -> calc_client_local_event

(** Local outputs: the response frame received from the server, delivered up. **)
type calc_client_local_output = CalcP.calc_frame

(**
  The client's step relation.

  On a `WireEvent resp` the client is awaiting a response: `resp` must be the
  server-predicted response for the pending request, the completed log advances,
  and `resp` is delivered to the application as a local output.

  On a `LocalEvent (CalcClientIssue b)` the (idle) client issues request `b`,
  which is emitted as a wire output; nothing is delivered to the application.
**)
let calc_client_step
  (st0:client_state_abs)
  (ev:SM.event client_wire_message calc_client_local_event)
  (st1:client_state_abs)
  (out:SM.step_output client_wire_message calc_client_local_output)
  : GTot prop =
  match ev with
  | SM.WireEvent resp ->
    client_recv_step_ok st0 st1 resp /\
    out.SM.so_wire_outputs == [] /\
    out.SM.so_local_outputs == [resp]
  | SM.LocalEvent (CalcClientIssue b) ->
    client_issue_step_ok st0 st1 b /\
    out.SM.so_wire_outputs == [b] /\
    out.SM.so_local_outputs == []

noextract
let calc_client_state_machine
  : SM.state_machine
      client_state_abs
      client_wire_message
      calc_client_local_event
      calc_client_local_output =
  {
    SM.sm_initial_state = initial_client;
    SM.sm_step = calc_client_step;
  }

noextract
let calc_client_wire_format_state_machine
  : WFSM.wire_format_state_machine
      client_state_abs
      client_wire_message
      calc_client_local_event
      calc_client_local_output =
  {
    WFSM.wfsm_state_machine = calc_client_state_machine;
    WFSM.wfsm_wire_format = CalcP.calc_frame_wire_format;
  }

(** ─────────────────────────────────────────────────────────────────────────
    Bridge: `client_single_step` implies the framework's `state_evolves`.
    Mirrors Calc.Server.CanonicalProtocol.lemma_calc_server_step_rel_state_ahead.
    ───────────────────────────────────────────────────────────────────────── **)

(** An issue step drives the framework state machine forward by one transition. **)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 20"
val lemma_issue_step_evolves
  (st0 st1:client_state_abs)
  (b:CalcP.calc_frame)
  : Lemma
      (requires client_issue_step_ok st0 st1 b)
      (ensures SM.state_evolves calc_client_state_machine st0 st1)
let lemma_issue_step_evolves st0 st1 b =
  let out : SM.step_output client_wire_message calc_client_local_output = {
    SM.so_wire_outputs = [b];
    SM.so_local_outputs = [];
  } in
  let tr : SM.transition client_state_abs client_wire_message
                          calc_client_local_event calc_client_local_output = {
    SM.tr_event = SM.LocalEvent (CalcClientIssue b);
    SM.tr_next_state = st1;
    SM.tr_output = out;
  } in
  assert (calc_client_step st0 (SM.LocalEvent (CalcClientIssue b)) st1 out);
  assert (SM.trace_reaches calc_client_state_machine st0 [tr] st1);
  assert (exists trace. SM.trace_reaches calc_client_state_machine st0 trace st1)
#pop-options

(** A receive step drives the framework state machine forward by one transition. **)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 40"
val lemma_recv_step_evolves
  (st0 st1:client_state_abs)
  (rb:bytes)
  : Lemma
      (requires client_recv_step_ok st0 st1 rb)
      (ensures SM.state_evolves calc_client_state_machine st0 st1)
let lemma_recv_step_evolves st0 st1 rb =
  let pend = Some?.v st0.pending in
  let resp_frame : CalcP.calc_frame = CalcP.calc_frame_response_for st0.completed pend in
  // `rb` is (Seq.equal to) the predicted response frame; the network step's only
  // dependence on the received bytes is `Seq.equal response_for actual_output`,
  // so the same step holds with the canonical `resp_frame`.
  assert (Seq.equal resp_frame rb);
  assert (client_recv_step_ok st0 st1 resp_frame);
  let out : SM.step_output client_wire_message calc_client_local_output = {
    SM.so_wire_outputs = [];
    SM.so_local_outputs = [resp_frame];
  } in
  let tr : SM.transition client_state_abs client_wire_message
                          calc_client_local_event calc_client_local_output = {
    SM.tr_event = SM.WireEvent resp_frame;
    SM.tr_next_state = st1;
    SM.tr_output = out;
  } in
  assert (calc_client_step st0 (SM.WireEvent resp_frame) st1 out);
  assert (SM.trace_reaches calc_client_state_machine st0 [tr] st1);
  assert (exists trace. SM.trace_reaches calc_client_state_machine st0 trace st1)
#pop-options

(**
  Every `client_single_step` is a one-transition evolution of the canonical
  client state machine. This is the client analogue of the server's
  `lemma_calc_server_step_rel_state_ahead`, and lets the low-level `Calc.Client`
  operation postconditions (`client_single_step`) plug into the framework
  instance directly.
**)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 40"
val lemma_client_single_step_evolves
  (st0 st1:client_state_abs)
  : Lemma
      (requires client_single_step st0 st1)
      (ensures SM.state_evolves calc_client_state_machine st0 st1)
let lemma_client_single_step_evolves st0 st1 =
  eliminate
    (exists (b:client_frame). client_issue_step_ok st0 st1 b) \/
    (exists (rb:bytes). client_recv_step_ok st0 st1 rb)
  with
    eliminate exists (b:client_frame). client_issue_step_ok st0 st1 b
    with lemma_issue_step_evolves st0 st1 b
  and
    eliminate exists (rb:bytes). client_recv_step_ok st0 st1 rb
    with lemma_recv_step_evolves st0 st1 rb
#pop-options
