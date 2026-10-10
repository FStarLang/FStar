module Calc.Client.Log

(**
  Abstract client-side state machine for the calculator protocol.

  This is the client-side mirror of the server's ghost-log pattern (`Calc.Log` +
  `Calc.Impl.Types.server_exactly`). Where the server *receives* requests and
  *sends* responses, the client *sends* requests and *receives* responses.

  The client tracks the same layered log as the server, but from the mirrored
  direction, plus a small two-phase state machine:

    - `ClientIdle`       : ready to issue the next request
    - `ClientAwaiting b` : has sent request bytes `b`, awaiting its response

  The completed round-trips are modelled by reusing the server-side `calc_log`
  (a "predicted server" view), so all of `Calc.Log`'s consistency machinery is
  reused directly.
**)

module L = FStar.List.Tot
module Seq = FStar.Seq
module R = FStar.ReflexiveTransitiveClosure
module SM = Pulse.Lib.Protocol.StateMachine
module CalcP = Calc.Protocol

open FStar.Preorder
open FStar.List.Tot
open Calc.Spec
open Calc.Wire
open Calc.Log

(** A well-formed request frame on the wire (same refinement as the server's). **)
type client_frame = CalcP.calc_frame

(** The client's phase. **)
type client_phase =
  | ClientIdle
  | ClientAwaiting : client_frame -> client_phase

(**
  Abstract client state.

  `completed` is the predicted-server view of every fully-completed round-trip
  (request issued *and* its response received). `pending`, when present, is the
  wire bytes of a request that has been sent but whose response has not yet been
  received.
**)
noeq
type client_state_abs = {
  completed: calc_log;
  pending: option client_frame;
}

let client_phase_of (st:client_state_abs) : client_phase =
  match st.pending with
  | None -> ClientIdle
  | Some b -> ClientAwaiting b

(** Initial client: nothing sent, nothing pending. **)
let initial_client : client_state_abs = {
  completed = initial_log;
  pending = None;
}

(** For a well-formed frame, `parse_request` really does succeed. **)
val lemma_client_frame_request_some (b:client_frame)
  : Lemma (parse_request b == Some (CalcP.calc_frame_request b))
let lemma_client_frame_request_some b = ()

(** All requests the client has issued (completed ones, plus any pending one). **)
let issued_requests (st:client_state_abs) : list request =
  match st.pending with
  | None -> st.completed.requests
  | Some b -> st.completed.requests @ [CalcP.calc_frame_request b]

(** Bytes the client has sent (its requests). **)
let client_sent_bytes (st:client_state_abs) : bytes =
  match st.pending with
  | None -> st.completed.input_bytes
  | Some b -> Seq.append st.completed.input_bytes b

(** Bytes the client has received (its responses). **)
let client_recv_bytes (st:client_state_abs) : bytes =
  st.completed.output_bytes

(**
  Semantic consistency of the client: the completed round-trips form a
  consistent server log. (Response-side wire correspondence is included here.)
**)
let client_consistent (st:client_state_abs) : prop =
  log_consistent st.completed

(**
  Full layered wire correspondence for the client:
    - the bytes it sent parse back to exactly the requests it issued;
    - the bytes it received are exactly the serialization of the responses it got.
**)
let client_wire_correspondence (st:client_state_abs) : prop =
  Seq.length (client_sent_bytes st) % 5 == 0 /\
  all_parse (client_sent_bytes st) /\
  parse_requests (client_sent_bytes st) == issued_requests st /\
  (serialize_responses st.completed.responses `Seq.equal` client_recv_bytes st)

(** ─────────────────────────────────────────────────────────────────────────
    Transitions
    ───────────────────────────────────────────────────────────────────────── **)

(** Issue a request: Idle -> Awaiting. Appends `b` to the sent bytes. **)
let client_issue (b:client_frame) (st:client_state_abs{None? st.pending})
  : client_state_abs =
  { st with pending = Some b }

(** The completed-log after receiving the pending request's response. **)
let recv_completed (st:client_state_abs{Some? st.pending}) : calc_log =
  let b = Some?.v st.pending in
  let req = CalcP.calc_frame_request b in
  let (new_state, resp) = step st.completed.current_state req in
  {
    input_bytes = Seq.append st.completed.input_bytes b;
    output_bytes = Seq.append st.completed.output_bytes (serialize_response resp);
    requests = st.completed.requests @ [req];
    responses = st.completed.responses @ [resp];
    current_state = new_state;
  }

(** Receive the pending request's response: Awaiting -> Idle. **)
let client_recv (st:client_state_abs{Some? st.pending}) : client_state_abs =
  { completed = recv_completed st; pending = None }

(** ─────────────────────────────────────────────────────────────────────────
    Step relations and monotonic evolution (mirrors log_single_step/log_evolves)
    ───────────────────────────────────────────────────────────────────────── **)

let client_issue_step_ok (st0 st1:client_state_abs) (b:client_frame) : prop =
  None? st0.pending /\ st1 == client_issue b st0

(**
  A receive step is legal when the pending request's response, as predicted by
  the server semantics, is exactly the `rb` bytes the client received.
**)
let client_recv_step_ok (st0 st1:client_state_abs) (rb:bytes) : prop =
  Some? st0.pending /\
  None? st1.pending /\
  Seq.length rb == 5 /\
  CalcP.calc_frame_network_step_ok st0.completed (Some?.v st0.pending) st1.completed rb

let client_single_step : R.binrel client_state_abs =
  fun st0 st1 ->
    (exists (b:client_frame). client_issue_step_ok st0 st1 b) \/
    (exists (rb:bytes). client_recv_step_ok st0 st1 rb)

let client_evolves : preorder client_state_abs = R.closure client_single_step

let valid_client (st:client_state_abs) : prop = client_evolves initial_client st

(** ─────────────────────────────────────────────────────────────────────────
    Lemmas
    ───────────────────────────────────────────────────────────────────────── **)

(** The initial client is consistent and its (empty) wire logs correspond. **)
val lemma_initial_client
  : unit -> Lemma (client_consistent initial_client /\
                   client_wire_correspondence initial_client)
let lemma_initial_client () =
  lemma_initial_log_consistent ()

(**
  Issuing a request preserves consistency and wire correspondence. This is the
  one non-trivial correspondence step: appending the new request bytes to the
  sent stream must still parse back to the issued-requests list.
**)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 40"
val lemma_client_issue_correspondence
  (b:client_frame)
  (st:client_state_abs{None? st.pending /\
                       client_consistent st /\
                       client_wire_correspondence st})
  : Lemma (client_consistent (client_issue b st) /\
           client_wire_correspondence (client_issue b st))
let lemma_client_issue_correspondence b st =
  let req = CalcP.calc_frame_request b in
  let st1 = client_issue b st in
  lemma_client_frame_request_some b;
  // Sent bytes grow by the 5-byte request frame `b`.
  lemma_parse_requests_single b req;
  lemma_parse_requests_append_one st.completed.input_bytes b req;
  lemma_all_parse_append st.completed.input_bytes b;
  assert (Seq.equal (client_sent_bytes st1)
                    (Seq.append st.completed.input_bytes b));
  assert (parse_requests (client_sent_bytes st1) == issued_requests st1)
#pop-options

(**
  The receive step is a legal `client_single_step`: the pending request's
  predicted response frame drives the completed log forward exactly as the
  server's network step would.
**)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 40"
val lemma_client_recv_step_ok
  (st:client_state_abs{Some? st.pending})
  : Lemma
      (client_recv_step_ok st (client_recv st)
        (CalcP.calc_frame_response_for st.completed (Some?.v st.pending)))
let lemma_client_recv_step_ok st =
  let b = Some?.v st.pending in
  lemma_client_frame_request_some b
#pop-options

(** The receive step is one of the abstract state machine's steps. **)
val lemma_client_recv_single_step
  (st:client_state_abs{Some? st.pending})
  : Lemma
      (client_single_step st (client_recv st))
let lemma_client_recv_single_step st =
  lemma_client_recv_step_ok st

(** The issue step is one of the abstract state machine's steps. **)
val lemma_client_issue_single_step
  (b:client_frame)
  (st:client_state_abs{None? st.pending})
  : Lemma
      (client_single_step st (client_issue b st))
let lemma_client_issue_single_step b st = ()

(** ─────────────────────────────────────────────────────────────────────────
    The client as a `Pulse.Lib.Protocol.StateMachine.state_machine`

    The server already is one (`Calc.Protocol.calc_frame_state_machine`, over
    `calc_log`).  Giving the client one too — over the SAME wire type
    `CalcP.calc_frame` — means both endpoints speak a single wire language, and
    lets the combined system be obtained as an instance of the generic
    `Pulse.Lib.Protocol.MachineProduct` construction instead of hand-writing the move
    families a second time.

    The two step relations are exactly the two relations already defined above:
    a LOCAL `ClientIssue b` event issues request frame `b` (and emits it on the
    wire), and a WIRE event on a response frame `rb` completes the round trip
    (and emits nothing).
    ───────────────────────────────────────────────────────────────────────── **)

(** The client's local (application-driven) events: issue a request frame. **)
type calc_client_local_event =
  | ClientIssue : client_frame -> calc_client_local_event

(** The client's step relation. **)
let calc_client_step
  (st0:client_state_abs)
  (ev:SM.event CalcP.calc_frame calc_client_local_event)
  (st1:client_state_abs)
  (out:SM.step_output CalcP.calc_frame unit)
  : GTot prop =
  match ev with
  | SM.LocalEvent (ClientIssue b) ->
    client_issue_step_ok st0 st1 b /\
    out.SM.so_wire_outputs == [b] /\
    out.SM.so_local_outputs == []
  | SM.WireEvent rb ->
    client_recv_step_ok st0 st1 rb /\
    out.SM.so_wire_outputs == [] /\
    out.SM.so_local_outputs == []

noextract
let calc_client_state_machine
  : SM.state_machine client_state_abs CalcP.calc_frame calc_client_local_event unit =
  {
    SM.sm_initial_state = initial_client;
    SM.sm_step = calc_client_step;
  }
