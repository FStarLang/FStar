module Calc.System

(**
  The combined calculator client–server system.

  This composes the verified client (`Calc.Client.Log`) and server
  (`Calc.Log`) abstract state machines into a single transition system with an
  explicit message channel, so that temporal properties of their *interaction*
  can be stated and proved (see `Calc.System.Temporal`).

  The protocol is strict request/response lockstep, so at most one message is
  ever in flight; the channel is:

    - `MP.Quiet`      : nothing in flight (the system is quiescent);
    - `MP.ToServer b` : the client has sent request frame `b`, the server has
                        not yet processed it;
    - `MP.ToClient r` : the server has produced response frame `r`, the client
                        has not yet received it.

  The three transitions are `issue` (client sends a request), `serve` (server
  processes the in-flight request) and `recv` (client receives the response).

  The key structural invariant (`system_inv`, proved inductive below) pins down
  exactly how the two endpoints lag during delivery:

    - `MP.Quiet`/`MP.ToServer`: the server log equals the client's completed
      log (so the stacks agree);
    - `MP.ToClient`: the server has advanced one request ahead of the client's
      completed log.
**)

module R = FStar.ReflexiveTransitiveClosure
module Seq = FStar.Seq
module CalcP = Calc.Protocol
module MP = Pulse.Lib.Protocol.MachineProduct
module SM = Pulse.Lib.Protocol.StateMachine

open Calc.Spec
open Calc.Wire
open Calc.Log
open Calc.Client.Log
open FStar.List.Tot

(** ─────────────────────────────────────────────────────────────────────────
    States
    ───────────────────────────────────────────────────────────────────────── **)

(** The in-flight payload: a well-formed calculator frame (request or
    response bytes).  The CHANNEL and the SYSTEM STATE themselves are no longer
    declared here: they are the generic ones from `Pulse.Lib.Protocol.MachineProduct`, whose
    constructors are `MP.Quiet` / `MP.ToServer` / `MP.ToClient` and whose record
    fields are already named `client` / `server` / `channel`. **)
let calc_payload = CalcP.calc_frame

(** The combined system state: client, server, and the channel between them. **)
type system_state = MP.sys client_state_abs calc_log calc_payload

(** The stacks we ultimately want to compare. **)
let client_stack (s:system_state) : calc_stack = s.client.completed.current_state
let server_stack (s:system_state) : calc_stack = s.server.current_state

(** The system is quiescent when nothing is in flight. **)
let quiescent (s:system_state) : prop = MP.Quiet? s.channel

(** ─────────────────────────────────────────────────────────────────────────
    The server processing a single request frame (mirrors recv_completed).
    ───────────────────────────────────────────────────────────────────────── **)

(** The server log after processing request frame `b`. **)
let server_process (srv:calc_log) (b:CalcP.calc_frame) : calc_log =
  let req = CalcP.calc_frame_request b in
  let (new_state, resp) = step srv.current_state req in
  {
    input_bytes   = Seq.append srv.input_bytes b;
    output_bytes  = Seq.append srv.output_bytes (serialize_response resp);
    requests      = srv.requests @ [req];
    responses     = srv.responses @ [resp];
    current_state = new_state;
  }

(**
  `server_process` on a client's completed log is exactly the client's own
  `recv_completed`: they are the same computation. This equality is what makes
  the `recv` transition re-establish `server == client.completed`.
**)
val lemma_recv_completed_eq (st:client_state_abs{Some? st.pending})
  : Lemma (recv_completed st == server_process st.completed (Some?.v st.pending))
let lemma_recv_completed_eq st = ()

(** ─────────────────────────────────────────────────────────────────────────
    Transitions (as total functions; guarded by the step relation below)
    ───────────────────────────────────────────────────────────────────────── **)

(** Client issues request frame `b` (only meaningful when Quiet & Idle). **)
let do_issue (b:CalcP.calc_frame) (s:system_state) : system_state =
  if MP.Quiet? s.channel && None? s.client.pending
  then { s with client = client_issue b s.client; channel = MP.ToServer b }
  else s

(** Server processes the in-flight request. **)
let do_serve (s:system_state) : system_state =
  match s.channel with
  | MP.ToServer b ->
    { s with
      server  = server_process s.server b;
      channel = MP.ToClient (CalcP.calc_frame_response_for s.server b) }
  | _ -> s

(** Client receives the in-flight response (only meaningful when awaiting). **)
let do_recv (s:system_state) : system_state =
  if MP.ToClient? s.channel && Some? s.client.pending
  then { s with client = client_recv s.client; channel = MP.Quiet }
  else s

(** ─────────────────────────────────────────────────────────────────────────
    The system step relation
    ───────────────────────────────────────────────────────────────────────── **)

(** The calculator system as an instance of the generic MACHINE product
    (`Pulse.Lib.Protocol.MachineProduct`), which itself feeds `Pulse.Lib.Protocol.SystemProduct`'s
    single-slot directed-channel discipline.

    Nothing about message delivery is written here any more.  We supply only the
    two endpoint state machines — the client's `calc_client_state_machine` and
    the server's `CalcP.calc_frame_state_machine`, both over the SAME wire type
    `CalcP.calc_frame` — plus the tiny channel interface: an emission puts its
    single wire output in flight (`emit_c` / `emit_s`), and an in-flight payload
    delivers itself verbatim (`carries` is equality, this being a semantic
    channel).  The calculator is strict request/response, so
    `MP.request_response_moves` enables exactly `client_send`, `server_serve`
    (the fused receive-and-respond) and `deliver_to_client`.

    The seven move families, and hence `sys_step`, are then DERIVED: each is one
    `sm_step` of one endpoint plus channel bookkeeping. **)
let calc_machine_iface
  : MP.machine_iface
      client_state_abs calc_log calc_payload
      CalcP.calc_frame calc_client_local_event CalcP.calc_frame_local_event unit = {
  cstep   = calc_client_step;
  sstep   = CalcP.calc_frame_step;
  emit_c  = (fun _a _a' out p -> out.SM.so_wire_outputs == [p]);
  emit_s  = (fun _a _a' out p -> out.SM.so_wire_outputs == [p]);
  carries = (fun p w -> p == w);
  moves   = MP.request_response_moves;
}

(** Initial state: fresh client, fresh server, empty channel — the generic
    initial system at the two endpoints' own initial states. **)
let initial_system : system_state =
  MP.initial_sys initial_client initial_log

let sys_step : R.binrel system_state =
  fun s s' -> MP.machine_step calc_machine_iface s s'

(** Stutter-tolerant step: a real step or "no delivery yet". Used for runs where
    the environment may delay delivery (needed for the liveness statement). **)
let sys_step_stutter : R.binrel system_state =
  fun s s' -> sys_step s s' \/ s' == s

let reachable (s s':system_state) : prop = R.closure sys_step s s'

(** ─────────────────────────────────────────────────────────────────────────
    The structural invariant and its inductiveness
    ───────────────────────────────────────────────────────────────────────── **)

(**
  The invariant precisely describes the lag between client and server:
    - MP.Quiet / MP.ToServer: the server log equals the client's completed log;
    - MP.ToClient r: the server is one processed request ahead, and `r` is that
      request's response.
**)
let system_inv (s:system_state) : prop =
  match s.channel with
  | MP.Quiet ->
    None? s.client.pending /\
    s.server == s.client.completed
  | MP.ToServer b ->
    s.client.pending == Some b /\
    s.server == s.client.completed
  | MP.ToClient r ->
    Some? s.client.pending /\
    (let b = Some?.v s.client.pending in
     s.server == server_process s.client.completed b /\
     r == CalcP.calc_frame_response_for s.client.completed b)

val lemma_initial_inv : unit -> Lemma (system_inv initial_system)
let lemma_initial_inv () = ()

#push-options "--fuel 1 --ifuel 2 --z3rlimit 10"
val lemma_inv_preserved (s s':system_state)
  : Lemma (requires system_inv s /\ sys_step s s')
          (ensures system_inv s')
let lemma_inv_preserved s s' =
  // Case-split on the channel: the generic lemma tells us which derived move
  // families can possibly have fired.
  MP.lemma_step_channel_cases calc_machine_iface s s';
  match s.channel with
  | MP.Quiet ->
    // Only `mp_client_send` is enabled (the other three quiet-gated families
    // are disabled by `request_response_moves`).  Unfolding it exposes a single
    // `calc_client_step` on a `ClientIssue b` local event, whose
    // `client_issue_step_ok` supplies the `None? s.client.pending` guard that
    // used to be written by hand in the product.
    ()
  | MP.ToServer b ->
    // Only `mp_server_serve` is enabled.  Note it no longer carries the
    // cross-endpoint guard relating the in-flight frame to `s.client.pending`;
    // that fact is recovered from `system_inv s`, which at `ToServer b` already
    // says `s.client.pending == Some b`.
    ()
  | MP.ToClient r ->
    // Only `mp_deliver_to_client` is enabled; `client_recv_step_ok` supplies
    // `Some? s.client.pending`, and the client's completed log catches up with
    // the server's.
    lemma_recv_completed_eq s.client;
    ()
#pop-options

(** The invariant holds on every reachable state. **)
val lemma_reachable_inv (s:system_state)
  : Lemma (requires reachable initial_system s)
          (ensures system_inv s)
let lemma_reachable_inv s =
  lemma_initial_inv ();
  Classical.forall_intro_2
    (Classical.move_requires_2 lemma_inv_preserved);
  R.stable_on_closure sys_step system_inv ()
