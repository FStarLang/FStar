module TFTP.Impl.Client.Log

(**
  Pure ghost-log / reachable-trace machinery for the TFTP *client* (receiver)
  `Pulse.Lib.Protocol.Implementation.protocol_implementation` instance, refined
  against the reliable-delivery (stop-and-wait ARQ) spec state machine
  `TFTP.Protocol.tftp_client_wfsm`.

  This is the receiver analogue of `TFTP.Impl.Server.Log`: the client CONSUMES
  wire input (indexed DATA datagrams and ERROR datagrams) and EMITS wire output
  (a `Msg_ack blk` on every DATA block).  So a single DATA `WireEvent` grows BOTH
  byte histories: `tcl_received` by the consumed DATA datagram and `tcl_sent` by
  the emitted ACK.  An ERROR datagram grows only `tcl_received` (it emits
  nothing), and the sole local event `Client_start` initialises the receiver
  (setting the filename) and touches neither history.

  ── How the client discharges `valid_byte_trace` (the crux) ─────────────────

  TFTP has NO `wire_format_stream_laws` instance because DATA is
  datagram-delimited (its payload length is the enclosing UDP datagram's length),
  hence DATA is NOT a strong (prefix) parser: a multi-block receiver could never
  satisfy the whole-stream greedy `parses_as` refinement.  The TFTP *server* Log
  sidesteps this because it only ever consumes ACK/ERROR (both self-delimiting
  prefix parsers) and can therefore re-derive `parses_as`.  The CLIENT cannot —
  it consumes DATA.

  Instead the client uses the DATAGRAM (serialize-equality) disjunct that
  `Pulse.Lib.Protocol.WireFormatStateMachine.valid_byte_trace` now accepts on its input side:

      Seq.equal input_bytes (Seq.append (serialize_all (trace_input_messages trace)) residual)

  which is the faithful refinement for a datagram transport (one datagram per
  `read`, the boundaries supplied by the framing, not the bytes).  This is the
  *forward* direction — the received stream is exactly the concatenation of the
  serializations of the consumed messages — preserved incrementally by appending
  one WireEvent at a time (`serialize_all (inputs ++ [m]) == serialize_all inputs
  ++ serialize m`).  So `client_trace_ok` carries a plain serialize-equality
  witness (no `all_*_inputs_ok`, no `parses_as`), and `lemma_client_trace_ok_valid`
  chooses the datagram disjunct with residual `Seq.empty`.

  All of this is pure F* (no Pulse); the Pulse instance in
  `TFTP.Impl.Client.CanonicalProtocol` allocates a monotonic ghost reference over
  `tc_state_ahead_preorder` and folds `client_trace_ok` into its invariant.
  Verified but NOT extracted.
**)

module L = FStar.List.Tot
module Seq = FStar.Seq
module SP = FStar.Seq.Properties
module ID = FStar.IndefiniteDescription
module Pre = FStar.Preorder
module RTC = FStar.ReflexiveTransitiveClosure
module SZ = FStar.SizeT
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module E = FStar.Endianness

module SM = Pulse.Lib.Protocol.StateMachine
module WF = Pulse.Lib.Protocol.WireFormat
module WFSM = Pulse.Lib.Protocol.WireFormatStateMachine
module TCP = Pulse.Lib.TCP
module CPI = Pulse.Lib.Protocol.Implementation
module FT = Pulse.Lib.Protocol.FileTransfer

module TP = TFTP.Protocol
module Codec = TFTP.Impl.Codec

open TFTP.Wire

#set-options "--fuel 2 --ifuel 2 --z3rlimit 20"

(* ───────────────────────────────────────────────────────────────────────────
   The receiver ghost log
   ─────────────────────────────────────────────────────────────────────────── *)

noeq
type tftp_client_log = {
  tcl_received : TCP.bytes;               // all wire bytes received (DATA/ERROR datagrams)
  tcl_sent     : TCP.bytes;               // wire output bytes (emitted ACK packets)
  tcl_state    : TP.tftp_client_state;    // abstract spec state
}

(* The log is fully determined by the (received, sent, state) triple. *)
noextract
let mk_log (received sent:TCP.bytes) (st:TP.tftp_client_state) : tftp_client_log =
  { tcl_received = received; tcl_sent = sent; tcl_state = st }

(* Agreement between the concrete 1-cell status flag carried by the Pulse handle
   and the abstract state.  Four runtime values, because the ARQ receiver is born
   *un-started* (the initial state has `tcs_filename == None`) and the concrete
   `Client_start` step must be distinguishable from the started/in-progress state
   (both are `FT_InProgress`):

     0uy  not-yet-started   (tcs_filename == None,   FT_InProgress)
     1uy  started/receiving (Some? tcs_filename,     FT_InProgress)
     2uy  completed         (Some? tcs_filename,     FT_Completed)
     3uy  aborted           (Some? tcs_filename,     FT_Aborted)  *)
noextract
let tc_status_flag_ok (s:U8.t) (st:TP.tftp_client_state) : prop =
  (s == 0uy /\ st.TP.tcs_status == FT.FT_InProgress /\ st.TP.tcs_filename == None) \/
  (s == 1uy /\ st.TP.tcs_status == FT.FT_InProgress /\ Some? st.TP.tcs_filename) \/
  (s == 2uy /\ st.TP.tcs_status == FT.FT_Completed  /\ Some? st.TP.tcs_filename) \/
  (s == 3uy /\ st.TP.tcs_status == FT.FT_Aborted    /\ Some? st.TP.tcs_filename)

noextract
let client_trace =
  list (SM.transition TP.tftp_client_state tftp_message TP.tftp_client_local unit)

(* ───────────────────────────────────────────────────────────────────────────
   Generic serialize / trace list-append lemmas  (copy-verbatim from the server)
   ─────────────────────────────────────────────────────────────────────────── *)

(* Serializing a list is the concatenation of serializing the two halves. *)
let rec lemma_serialize_all_append
  (#msg:Type0) (fmt:WF.wire_format msg) (l1 l2:list msg)
  : Lemma
      (ensures
        Seq.equal
          (WF.serialize_all fmt (L.append l1 l2))
          (Seq.append (WF.serialize_all fmt l1) (WF.serialize_all fmt l2)))
      (decreases l1)
=
  match l1 with
  | [] -> Seq.append_empty_l (WF.serialize_all fmt l2)
  | x :: r ->
    lemma_serialize_all_append fmt r l2;
    Seq.lemma_eq_elim
      (WF.serialize_all fmt (L.append r l2))
      (Seq.append (WF.serialize_all fmt r) (WF.serialize_all fmt l2));
    Seq.append_assoc
      (fmt.WF.wf_serialize x)
      (WF.serialize_all fmt r)
      (WF.serialize_all fmt l2)

(* serialize_all of a singleton is just the serialization of that element. *)
let lemma_tftp_serialize_all_singleton (msg:tftp_message)
  : Lemma (WF.serialize_all tftp_wire_format [msg] == tftp_serialize msg)
=
  Seq.append_empty_r (tftp_serialize msg)

(* The wire outputs of a concatenated trace is the concatenation of the wire
   outputs. *)
let rec lemma_trace_wire_outputs_append
  (#st #wm #le #lo:Type0)
  (t1 t2:list (SM.transition st wm le lo))
  : Lemma
      (ensures
        SM.trace_wire_outputs (L.append t1 t2) ==
        L.append (SM.trace_wire_outputs t1) (SM.trace_wire_outputs t2))
      (decreases t1)
=
  match t1 with
  | [] -> ()
  | tr :: rest ->
    lemma_trace_wire_outputs_append rest t2;
    L.append_assoc
      tr.SM.tr_output.SM.so_wire_outputs
      (SM.trace_wire_outputs rest)
      (SM.trace_wire_outputs t2)

(* Likewise for the input messages. *)
let rec lemma_trace_input_messages_append
  (#st #wm #le #lo:Type0)
  (t1 t2:list (SM.transition st wm le lo))
  : Lemma
      (ensures
        WFSM.trace_input_messages (L.append t1 t2) ==
        L.append (WFSM.trace_input_messages t1) (WFSM.trace_input_messages t2))
      (decreases t1)
=
  match t1 with
  | [] -> ()
  | tr :: rest ->
    lemma_trace_input_messages_append rest t2;
    L.append_assoc
      (WFSM.event_input_messages tr.SM.tr_event)
      (WFSM.trace_input_messages rest)
      (WFSM.trace_input_messages t2)

(* ───────────────────────────────────────────────────────────────────────────
   Single-step relation + its RTC-closure preorder

   ONE unified step: some event `ev` carries `log0` to `log1`, growing the
   received history by the serialized input messages of `ev`
   (`serialize_all [msg]` for a WireEvent, `Seq.empty` for a LocalEvent) and the
   sent history by the serialized wire outputs of the step.
   ─────────────────────────────────────────────────────────────────────────── *)

noextract
let tc_step_body
  (log0 log1:tftp_client_log)
  (ev:SM.event tftp_message TP.tftp_client_local)
  (out:SM.step_output tftp_message unit)
  : prop =
  TP.tftp_client_step log0.tcl_state ev log1.tcl_state out /\
  Seq.equal log1.tcl_received
    (Seq.append log0.tcl_received
       (WF.serialize_all tftp_wire_format (WFSM.event_input_messages ev))) /\
  Seq.equal log1.tcl_sent
    (Seq.append log0.tcl_sent
       (WF.serialize_all tftp_wire_format out.SM.so_wire_outputs))

noextract
let tc_step_rel (log0 log1:tftp_client_log) : prop =
  exists ev out. tc_step_body log0 log1 ev out

(* Introduce a step from concrete witnesses (SMT existential intro). *)
let lemma_tc_step_rel_intro
  (log0 log1:tftp_client_log)
  (ev:SM.event tftp_message TP.tftp_client_local)
  (out:SM.step_output tftp_message unit)
  : Lemma (requires tc_step_body log0 log1 ev out) (ensures tc_step_rel log0 log1)
=
  ()

noextract
let tc_state_ahead_preorder : Pre.preorder tftp_client_log =
  RTC.closure tc_step_rel

(* ── state_ahead: a single step advances the state machine ────────────────── *)

let lemma_tc_step_state_ahead (log0 log1:tftp_client_log)
  : Lemma
      (requires tc_step_rel log0 log1)
      (ensures CPI.state_ahead TP.tftp_client_wfsm log0.tcl_state log1.tcl_state)
=
  let ev =
    ID.indefinite_description_ghost
      (SM.event tftp_message TP.tftp_client_local)
      (fun ev -> exists out. tc_step_body log0 log1 ev out) in
  let out =
    ID.indefinite_description_ghost
      (SM.step_output tftp_message unit)
      (fun out -> tc_step_body log0 log1 ev out) in
  let tr : SM.transition TP.tftp_client_state tftp_message TP.tftp_client_local unit =
    { SM.tr_event = ev; SM.tr_next_state = log1.tcl_state; SM.tr_output = out } in
  assert (SM.trace_reaches
    TP.tftp_client_wfsm.WFSM.wfsm_state_machine log0.tcl_state [tr] log1.tcl_state);
  assert (exists trace.
    SM.trace_reaches
      TP.tftp_client_wfsm.WFSM.wfsm_state_machine log0.tcl_state trace log1.tcl_state)

let lemma_tc_closure_state_ahead (log0 log1:tftp_client_log)
  : Lemma
      (requires tc_state_ahead_preorder log0 log1)
      (ensures CPI.state_ahead TP.tftp_client_wfsm log0.tcl_state log1.tcl_state)
=
  RTC.induct
    tc_step_rel
    (fun x y -> CPI.state_ahead TP.tftp_client_wfsm x.tcl_state y.tcl_state)
    (fun x ->
      SM.lemma_state_evolves_refl
        TP.tftp_client_wfsm.WFSM.wfsm_state_machine x.tcl_state)
    (fun x y -> lemma_tc_step_state_ahead x y)
    (fun x y z ->
      SM.lemma_state_evolves_trans
        TP.tftp_client_wfsm.WFSM.wfsm_state_machine x.tcl_state y.tcl_state z.tcl_state)
    log0
    log1
    ()

(* ── histories_ahead: a single step extends both byte histories ───────────── *)

let lemma_tc_step_histories_ahead (log0 log1:tftp_client_log)
  : Lemma
      (requires tc_step_rel log0 log1)
      (ensures
        TCP.bytes_extends log0.tcl_received log1.tcl_received /\
        TCP.bytes_extends log0.tcl_sent log1.tcl_sent)
=
  let ev =
    ID.indefinite_description_ghost
      (SM.event tftp_message TP.tftp_client_local)
      (fun ev -> exists out. tc_step_body log0 log1 ev out) in
  let out =
    ID.indefinite_description_ghost
      (SM.step_output tftp_message unit)
      (fun out -> tc_step_body log0 log1 ev out) in
  CPI.lemma_bytes_extends_append_equal
    log0.tcl_received log1.tcl_received
    (WF.serialize_all tftp_wire_format (WFSM.event_input_messages ev));
  CPI.lemma_bytes_extends_append_equal
    log0.tcl_sent log1.tcl_sent
    (WF.serialize_all tftp_wire_format out.SM.so_wire_outputs)

let lemma_tc_closure_histories_ahead (log0 log1:tftp_client_log)
  : Lemma
      (requires tc_state_ahead_preorder log0 log1)
      (ensures
        TCP.bytes_extends log0.tcl_received log1.tcl_received /\
        TCP.bytes_extends log0.tcl_sent log1.tcl_sent)
=
  RTC.induct
    tc_step_rel
    (fun x y ->
      TCP.bytes_extends x.tcl_received y.tcl_received /\
      TCP.bytes_extends x.tcl_sent y.tcl_sent)
    (fun x ->
      CPI.lemma_bytes_extends_refl x.tcl_received;
      CPI.lemma_bytes_extends_refl x.tcl_sent)
    (fun x y -> lemma_tc_step_histories_ahead x y)
    (fun x y z ->
      CPI.lemma_bytes_extends_trans x.tcl_received y.tcl_received z.tcl_received;
      CPI.lemma_bytes_extends_trans x.tcl_sent y.tcl_sent z.tcl_sent)
    log0
    log1
    ()

(* ───────────────────────────────────────────────────────────────────────────
   Canonical reachable-trace invariant
   ─────────────────────────────────────────────────────────────────────────── *)

noextract
let client_trace_witness
  (received sent:TCP.bytes)
  (log:tftp_client_log)
  (trace:client_trace)
  : prop =
  SM.trace_reaches
    TP.tftp_client_wfsm.WFSM.wfsm_state_machine
    TP.tftp_client_initial
    trace
    log.tcl_state /\
  Seq.equal
    received
    (WF.serialize_all tftp_wire_format (WFSM.trace_input_messages trace)) /\
  Seq.equal
    sent
    (WF.serialize_all tftp_wire_format (SM.trace_wire_outputs trace)) /\
  Seq.equal received log.tcl_received /\
  Seq.equal sent log.tcl_sent

noextract
let client_trace_ok
  (received sent:TCP.bytes)
  (log:tftp_client_log)
  : prop =
  exists trace. client_trace_witness received sent log trace

(* client_trace_ok refines the byte history into a valid state-machine trace.
   TFTP has no stream laws (DATA is datagram-delimited), so this chooses the
   DATAGRAM (serialize-equality) disjunct of `valid_byte_trace` with residual
   `Seq.empty` — the forward direction, which holds by construction. *)
let lemma_client_trace_ok_valid
  (received sent:TCP.bytes)
  (log:tftp_client_log)
  : Lemma
      (requires client_trace_ok received sent log)
      (ensures
        WFSM.valid_byte_trace
          TP.tftp_client_wfsm
          received
          log.tcl_state
          sent
          Seq.empty)
=
  let trace =
    ID.indefinite_description_ghost client_trace (client_trace_witness received sent log) in
  Seq.append_empty_r (WF.serialize_all tftp_wire_format (WFSM.trace_input_messages trace));
  assert (Seq.equal
    received
    (Seq.append
      (WF.serialize_all tftp_wire_format (WFSM.trace_input_messages trace))
      Seq.empty));
  assert (exists trace'.
    SM.trace_reaches
      TP.tftp_client_wfsm.WFSM.wfsm_state_machine
      TP.tftp_client_wfsm.WFSM.wfsm_state_machine.SM.sm_initial_state
      trace'
      log.tcl_state /\
    (WF.parses_as
       tftp_wire_format
       received
       (WFSM.trace_input_messages trace')
       Seq.empty
     \/
     Seq.equal
       received
       (Seq.append
         (WF.serialize_all tftp_wire_format (WFSM.trace_input_messages trace'))
         Seq.empty)) /\
    Seq.equal
      sent
      (WF.serialize_all tftp_wire_format (SM.trace_wire_outputs trace')))

(* The freshly-created (un-started) receiver at the initial state: reached by the
   empty trace, so both byte histories are empty. *)
let lemma_initial_trace_ok ()
  : Lemma
      (client_trace_ok Seq.empty Seq.empty
        (mk_log Seq.empty Seq.empty TP.tftp_client_initial))
=
  let trace : client_trace = [] in
  assert (SM.trace_reaches
    TP.tftp_client_wfsm.WFSM.wfsm_state_machine
    TP.tftp_client_initial
    trace
    TP.tftp_client_initial);
  Seq.lemma_eq_elim
    Seq.empty
    (WF.serialize_all tftp_wire_format (WFSM.trace_input_messages trace));
  Seq.lemma_eq_elim
    Seq.empty
    (WF.serialize_all tftp_wire_format (SM.trace_wire_outputs trace));
  assert (client_trace_witness Seq.empty Seq.empty
    (mk_log Seq.empty Seq.empty TP.tftp_client_initial) trace)

(* ───────────────────────────────────────────────────────────────────────────
   Extending the canonical trace by one step

   A generic single-transition extension: the byte histories grow by the
   serialized input messages of `ev` and the serialized wire outputs of the step.
   ─────────────────────────────────────────────────────────────────────────── *)

let lemma_client_trace_ok_step
  (received0 sent0:TCP.bytes)
  (st0:TP.tftp_client_state)
  (ev:SM.event tftp_message TP.tftp_client_local)
  (st1:TP.tftp_client_state)
  (out:SM.step_output tftp_message unit)
  : Lemma
      (requires
        client_trace_ok received0 sent0 (mk_log received0 sent0 st0) /\
        TP.tftp_client_step st0 ev st1 out)
      (ensures
        client_trace_ok
          (Seq.append received0
             (WF.serialize_all tftp_wire_format (WFSM.event_input_messages ev)))
          (Seq.append sent0
             (WF.serialize_all tftp_wire_format out.SM.so_wire_outputs))
          (mk_log
             (Seq.append received0
                (WF.serialize_all tftp_wire_format (WFSM.event_input_messages ev)))
             (Seq.append sent0
                (WF.serialize_all tftp_wire_format out.SM.so_wire_outputs))
             st1))
=
  let log0 = mk_log received0 sent0 st0 in
  let trace0 =
    ID.indefinite_description_ghost client_trace (client_trace_witness received0 sent0 log0) in
  let tr : SM.transition TP.tftp_client_state tftp_message TP.tftp_client_local unit =
    { SM.tr_event = ev; SM.tr_next_state = st1; SM.tr_output = out } in
  assert (SM.trace_reaches TP.tftp_client_state_machine st0 [tr] st1);
  SM.lemma_trace_reaches_append
    TP.tftp_client_wfsm.WFSM.wfsm_state_machine
    TP.tftp_client_initial st0 st1 trace0 [tr];
  let trace1 = L.append trace0 [tr] in
  (* input-message serialization grows by serialize_all (event_input_messages ev) *)
  lemma_trace_input_messages_append trace0 [tr];
  lemma_serialize_all_append
    tftp_wire_format (WFSM.trace_input_messages trace0) (WFSM.event_input_messages ev);
  Seq.lemma_eq_elim
    received0
    (WF.serialize_all tftp_wire_format (WFSM.trace_input_messages trace0));
  L.append_l_nil (WFSM.event_input_messages ev);
  (* wire-output serialization grows by serialize_all out.so_wire_outputs *)
  lemma_trace_wire_outputs_append trace0 [tr];
  lemma_serialize_all_append
    tftp_wire_format (SM.trace_wire_outputs trace0) out.SM.so_wire_outputs;
  Seq.lemma_eq_elim
    sent0
    (WF.serialize_all tftp_wire_format (SM.trace_wire_outputs trace0));
  L.append_l_nil out.SM.so_wire_outputs;
  let received1 =
    Seq.append received0
      (WF.serialize_all tftp_wire_format (WFSM.event_input_messages ev)) in
  let sent1 =
    Seq.append sent0
      (WF.serialize_all tftp_wire_format out.SM.so_wire_outputs) in
  assert (Seq.equal received1
    (WF.serialize_all tftp_wire_format (WFSM.trace_input_messages trace1)));
  assert (Seq.equal sent1
    (WF.serialize_all tftp_wire_format (SM.trace_wire_outputs trace1)));
  assert (client_trace_witness received1 sent1 (mk_log received1 sent1 st1) trace1)

(* ───────────────────────────────────────────────────────────────────────────
   process_result values, wire-output lists, step outputs, next-state helpers
   ─────────────────────────────────────────────────────────────────────────── *)

unfold
let tc_result (status:CPI.process_status) (consumed_len produced_len:SZ.t) : CPI.process_result =
  { CPI.process_status = status;
    CPI.process_consumed_len = consumed_len;
    CPI.process_produced_len = produced_len;
    CPI.process_app_len = 0sz }

noextract let no_wire_outputs : list tftp_message = []
noextract let ack_wire_outputs (blk:U16.t) : list tftp_message = [Msg_ack blk]
noextract let no_local_outputs : list unit = []

noextract
let empty_output : SM.step_output tftp_message unit =
  { SM.so_wire_outputs = no_wire_outputs; SM.so_local_outputs = no_local_outputs }
noextract
let ack_output (blk:U16.t) : SM.step_output tftp_message unit =
  { SM.so_wire_outputs = ack_wire_outputs blk; SM.so_local_outputs = no_local_outputs }

(* The started state Client_start installs (filename known, empty received). *)
noextract
let start_next_state (filename:TCP.bytes) : TP.tftp_client_state =
  { TP.tcs_filename = Some filename; TP.tcs_received = [];
    TP.tcs_status = FT.FT_InProgress }

(* Receiving one DATA block: append the payload; a short (< 512-byte) block ends
   the transfer. *)
noextract
let data_next_state (st0:TP.tftp_client_state) (pl:data_payload) : TP.tftp_client_state =
  { st0 with
    TP.tcs_received = L.append st0.TP.tcs_received [(pl <: TCP.bytes)];
    TP.tcs_status =
      (if Seq.length (pl <: TCP.bytes) < TP.tftp_block_size
       then FT.FT_Completed else FT.FT_InProgress) }

(* Receiving ERROR: abort (only the status flips). *)
noextract
let error_next_state (st0:TP.tftp_client_state) : TP.tftp_client_state =
  { st0 with TP.tcs_status = FT.FT_Aborted }

(* ───────────────────────────────────────────────────────────────────────────
   Step-witnesses: the enabled spec transitions
   ─────────────────────────────────────────────────────────────────────────── *)

let lemma_start_step (st0:TP.tftp_client_state) (filename:TCP.bytes)
  : Lemma
      (requires st0.TP.tcs_filename == None)
      (ensures
        TP.tftp_client_step st0 (SM.LocalEvent (TP.Client_start filename))
          (start_next_state filename) empty_output)
=
  ()

let lemma_data_step (st0:TP.tftp_client_state) (blk:U16.t) (pl:data_payload)
  : Lemma
      (requires Some? st0.TP.tcs_filename /\ st0.TP.tcs_status == FT.FT_InProgress)
      (ensures
        TP.tftp_client_step st0 (SM.WireEvent (Msg_data blk pl))
          (data_next_state st0 pl) (ack_output blk))
=
  ()

let lemma_error_step (st0:TP.tftp_client_state) (code:U16.t) (em:cstring)
  : Lemma
      (requires Some? st0.TP.tcs_filename /\ st0.TP.tcs_status == FT.FT_InProgress)
      (ensures
        TP.tftp_client_step st0 (SM.WireEvent (Msg_error code em))
          (error_next_state st0) empty_output)
=
  ()

(* ───────────────────────────────────────────────────────────────────────────
   Bridging a consumed datagram to its serialization (needed to append it to the
   trace).  These MIRROR the reasoning inside `TFTP.Impl.Codec.recv_data_exists`
   and the server's `lemma_input_is_serialize_error`.
   ─────────────────────────────────────────────────────────────────────────── *)

(* A ghost data_payload cut from a datagram tail (length bounded by 512). *)
noextract
let data_payload_of
  (inp:TCP.bytes)
  (n:nat{4 <= n /\ n <= 516 /\ Seq.length inp == n})
  : data_payload =
  Seq.slice inp 4 n

(* A 4+len DATA datagram whose fields are the observed bytes equals the
   serialization of the corresponding Msg_data. *)
let lemma_data_input_is_serialize (inp:TCP.bytes) (blk:U16.t) (pl:data_payload)
  : Lemma
      (requires
        Seq.length inp == 4 + Seq.length (pl <: TCP.bytes) /\
        Seq.index inp 0 == Codec.u16_hi op_data /\
        Seq.index inp 1 == Codec.u16_lo op_data /\
        blk == Codec.u16_of_bytes (Seq.index inp 2) (Seq.index inp 3) /\
        (forall (j:nat). j < Seq.length (pl <: TCP.bytes) ==>
           Seq.index (pl <: TCP.bytes) j == Seq.index inp (4 + j)))
      (ensures inp == tftp_serialize (Msg_data blk pl))
=
  Codec.lemma_enc16_bytes op_data;
  Codec.lemma_u16_of_bytes (Seq.index inp 2) (Seq.index inp 3);
  Codec.lemma_dec16_enc16
    (Seq.append (Seq.create 1 (Seq.index inp 2)) (Seq.create 1 (Seq.index inp 3)));
  Seq.lemma_eq_intro (tftp_serialize (Msg_data blk pl)) inp

(* A 5-byte minimal ERROR datagram equals the serialization of Msg_error code
   (empty message).  Other opcode-5 inputs fall to the sound no-op instead. *)
let lemma_error_input_is_serialize (inp:TCP.bytes) (code:U16.t)
  : Lemma
      (requires
        Seq.length inp == 5 /\
        Seq.index inp 0 == Codec.u16_hi op_error /\
        Seq.index inp 1 == Codec.u16_lo op_error /\
        code == Codec.u16_of_bytes (Seq.index inp 2) (Seq.index inp 3) /\
        Seq.index inp 4 == 0uy)
      (ensures inp == tftp_serialize (Msg_error code (Seq.empty <: cstring)))
=
  Codec.lemma_enc16_bytes op_error;
  Codec.lemma_u16_of_bytes (Seq.index inp 2) (Seq.index inp 3);
  Codec.lemma_dec16_enc16
    (Seq.append (Seq.create 1 (Seq.index inp 2)) (Seq.create 1 (Seq.index inp 3)));
  Seq.lemma_eq_intro (tftp_serialize (Msg_error code (Seq.empty <: cstring))) inp

(* ───────────────────────────────────────────────────────────────────────────
   Output-byte / produced helpers
   ─────────────────────────────────────────────────────────────────────────── *)

let lemma_output_written_empty (o:TCP.bytes)
  : Lemma (CPI.output_written o 0sz Seq.empty)
=
  assert (Seq.equal (CPI.output_prefix o 0sz) Seq.empty)

let lemma_empty_output_written (o:TCP.bytes)
  : Lemma (CPI.output_written o 0sz (WF.serialize_all tftp_wire_format no_wire_outputs))
=
  assert (WF.serialize_all tftp_wire_format no_wire_outputs == Seq.empty);
  lemma_output_written_empty o

(* If the first four bytes of the output buffer hold the ACK layout, then
   `output_written` holds for the serialized ACK at produced-length 4. *)
let lemma_ack_prefix_serialize (out_bytes:TCP.bytes) (blk:U16.t)
  : Lemma
      (requires
        Seq.length out_bytes >= 4 /\
        Seq.index out_bytes 0 == Codec.u16_hi op_ack /\
        Seq.index out_bytes 1 == Codec.u16_lo op_ack /\
        Seq.index out_bytes 2 == Codec.u16_hi blk /\
        Seq.index out_bytes 3 == Codec.u16_lo blk)
      (ensures CPI.output_written out_bytes 4sz (tftp_serialize (Msg_ack blk)))
=
  Codec.lemma_enc16_bytes op_ack;
  Codec.lemma_enc16_bytes blk;
  Seq.lemma_eq_intro (CPI.output_prefix out_bytes 4sz) (tftp_serialize (Msg_ack blk))

(* ───────────────────────────────────────────────────────────────────────────
   Advance lemmas: re-establish `client_trace_ok` and expose `tc_step_rel`
   ─────────────────────────────────────────────────────────────────────────── *)

(* DATA received: grow both histories (consumed datagram + emitted ACK). *)
let lemma_data_advance
  (received0 sent0:TCP.bytes) (st0:TP.tftp_client_state) (blk:U16.t) (pl:data_payload)
  : Lemma
      (requires
        client_trace_ok received0 sent0 (mk_log received0 sent0 st0) /\
        Some? st0.TP.tcs_filename /\ st0.TP.tcs_status == FT.FT_InProgress)
      (ensures (
        let received1 = Seq.append received0 (tftp_serialize (Msg_data blk pl)) in
        let sent1 = Seq.append sent0 (tftp_serialize (Msg_ack blk)) in
        let st1 = data_next_state st0 pl in
        client_trace_ok received1 sent1 (mk_log received1 sent1 st1) /\
        tc_step_rel (mk_log received0 sent0 st0) (mk_log received1 sent1 st1)))
=
  let st1 = data_next_state st0 pl in
  lemma_data_step st0 blk pl;
  lemma_tftp_serialize_all_singleton (Msg_data blk pl);
  lemma_tftp_serialize_all_singleton (Msg_ack blk);
  lemma_client_trace_ok_step received0 sent0 st0
    (SM.WireEvent (Msg_data blk pl)) st1 (ack_output blk);
  let received1 = Seq.append received0 (tftp_serialize (Msg_data blk pl)) in
  let sent1 = Seq.append sent0 (tftp_serialize (Msg_ack blk)) in
  lemma_tc_step_rel_intro (mk_log received0 sent0 st0) (mk_log received1 sent1 st1)
    (SM.WireEvent (Msg_data blk pl)) (ack_output blk)

(* ERROR received: grow only the received history (emits nothing). *)
let lemma_error_advance
  (received0 sent0:TCP.bytes) (st0:TP.tftp_client_state) (code:U16.t)
  : Lemma
      (requires
        client_trace_ok received0 sent0 (mk_log received0 sent0 st0) /\
        Some? st0.TP.tcs_filename /\ st0.TP.tcs_status == FT.FT_InProgress)
      (ensures (
        let received1 = Seq.append received0 (tftp_serialize (Msg_error code (Seq.empty <: cstring))) in
        client_trace_ok received1 sent0 (mk_log received1 sent0 (error_next_state st0)) /\
        tc_step_rel (mk_log received0 sent0 st0) (mk_log received1 sent0 (error_next_state st0))))
=
  let st1 = error_next_state st0 in
  let em : cstring = Seq.empty in
  lemma_error_step st0 code em;
  lemma_tftp_serialize_all_singleton (Msg_error code em);
  assert (WF.serialize_all tftp_wire_format no_wire_outputs == Seq.empty);
  lemma_client_trace_ok_step received0 sent0 st0 (SM.WireEvent (Msg_error code em)) st1 empty_output;
  Seq.append_empty_r sent0;
  let received1 = Seq.append received0 (tftp_serialize (Msg_error code em)) in
  lemma_tc_step_rel_intro (mk_log received0 sent0 st0) (mk_log received1 sent0 st1)
    (SM.WireEvent (Msg_error code em)) empty_output

(* ── local event (received unchanged; start emits nothing) ────────────────── *)

let lemma_start_advance
  (received0 sent0:TCP.bytes) (st0:TP.tftp_client_state) (filename:TCP.bytes)
  : Lemma
      (requires
        client_trace_ok received0 sent0 (mk_log received0 sent0 st0) /\
        st0.TP.tcs_filename == None)
      (ensures (
        let st1 = start_next_state filename in
        client_trace_ok received0 sent0 (mk_log received0 sent0 st1) /\
        tc_step_rel (mk_log received0 sent0 st0) (mk_log received0 sent0 st1)))
=
  let st1 = start_next_state filename in
  lemma_start_step st0 filename;
  assert (WF.serialize_all tftp_wire_format no_wire_outputs == Seq.empty);
  lemma_client_trace_ok_step received0 sent0 st0
    (SM.LocalEvent (TP.Client_start filename)) st1 empty_output;
  Seq.append_empty_r received0;
  Seq.append_empty_r sent0;
  lemma_tc_step_rel_intro (mk_log received0 sent0 st0) (mk_log received0 sent0 st1)
    (SM.LocalEvent (TP.Client_start filename)) empty_output

(* ───────────────────────────────────────────────────────────────────────────
   Process-correctness packaging (the pure postconditions of the handlers)
   ─────────────────────────────────────────────────────────────────────────── *)

let lemma_network_stepok
  (input:TCP.bytes) (input_len:SZ.t)
  (old_out out_bytes:TCP.bytes) (out_len:SZ.t)
  (received0 sent0:TCP.bytes) (st0:TP.tftp_client_state)
  (msg:tftp_message)
  (st1:TP.tftp_client_state)
  (produced_len:SZ.t)
  (wire_outputs:list tftp_message)
  (produced:TCP.bytes)
  : Lemma
      (requires
        CPI.buffers_wf input input_len old_out out_len /\
        Seq.length out_bytes == Seq.length old_out /\
        SZ.v input_len == Seq.length input /\
        input == tftp_serialize msg /\
        TP.tftp_client_step st0 (SM.WireEvent msg) st1
          ({ SM.so_wire_outputs = wire_outputs; SM.so_local_outputs = [] }) /\
        Seq.equal produced (WF.serialize_all tftp_wire_format wire_outputs) /\
        CPI.output_written out_bytes produced_len produced)
      (ensures
        CPI.network_process_correct TP.tftp_client_wfsm
          input input_len old_out out_bytes out_len
          received0 sent0 st0
          (tc_result CPI.StepOk input_len produced_len)
          (Seq.append received0 input) (Seq.append sent0 produced) st1
          input wire_outputs [])
=
  Seq.lemma_eq_elim (CPI.input_bytes input input_len) input;
  lemma_tftp_parse_serialize_exact msg;
  Seq.append_empty_r input;
  assert (CPI.step_output wire_outputs ([] <: list unit) ==
          ({ SM.so_wire_outputs = wire_outputs; SM.so_local_outputs = ([] <: list unit) }));
  assert (CPI.consumed_by_parse
            TP.tftp_client_wfsm.WFSM.wfsm_wire_format
            (CPI.input_bytes input input_len) msg input Seq.empty);
  assert (TP.tftp_client_wfsm.WFSM.wfsm_state_machine.SM.sm_step
            st0 (SM.WireEvent msg) st1 (CPI.step_output wire_outputs []));
  let result = tc_result CPI.StepOk input_len produced_len in
  assert_norm (result.CPI.process_status == CPI.StepOk);
  assert_norm (result.CPI.process_consumed_len == input_len);
  assert_norm (result.CPI.process_produced_len == produced_len);
  introduce exists (msg':tftp_message) (residual:TCP.bytes) (produced':TCP.bytes).
    CPI.consumed_by_parse
      TP.tftp_client_wfsm.WFSM.wfsm_wire_format
      (CPI.input_bytes input input_len) msg' input residual /\
    SZ.v result.CPI.process_consumed_len == Seq.length input /\
    TP.tftp_client_wfsm.WFSM.wfsm_state_machine.SM.sm_step
      st0 (SM.WireEvent msg') st1 (CPI.step_output wire_outputs []) /\
    Seq.equal produced' (WF.serialize_all TP.tftp_client_wfsm.WFSM.wfsm_wire_format wire_outputs) /\
    CPI.output_written out_bytes result.CPI.process_produced_len produced' /\
    Seq.equal (Seq.append received0 input) (Seq.append received0 input) /\
    Seq.equal (Seq.append sent0 produced) (Seq.append sent0 produced')
  with msg Seq.empty produced
  and ();
  match result.CPI.process_status with
  | CPI.StepOk ->
    assert (CPI.network_process_correct TP.tftp_client_wfsm
              input input_len old_out out_bytes out_len
              received0 sent0 st0
              result
              (Seq.append received0 input) (Seq.append sent0 produced) st1
              input wire_outputs [])
    by (
      FStar.Tactics.norm
        [delta_only [`%CPI.network_process_correct]; iota; zeta; primops];
      FStar.Tactics.smt ())
  | _ -> assert False

let lemma_local_stepok
  (ev:TP.tftp_client_local)
  (old_out out_bytes:TCP.bytes) (out_len:SZ.t)
  (received0 sent0:TCP.bytes) (st0:TP.tftp_client_state)
  (produced_len:SZ.t)
  (st1:TP.tftp_client_state)
  (wire_outputs:list tftp_message)
  (produced:TCP.bytes)
  : Lemma
      (requires
        SZ.v out_len == Seq.length old_out /\
        Seq.length out_bytes == Seq.length old_out /\
        TP.tftp_client_step st0 (SM.LocalEvent ev) st1
          ({ SM.so_wire_outputs = wire_outputs; SM.so_local_outputs = [] }) /\
        Seq.equal produced (WF.serialize_all tftp_wire_format wire_outputs) /\
        CPI.output_written out_bytes produced_len produced)
      (ensures
        CPI.local_process_correct TP.tftp_client_wfsm ev old_out out_bytes out_len
          received0 sent0 st0
          (tc_result CPI.StepOk 0sz produced_len)
          received0
          (Seq.append sent0 produced)
          st1 wire_outputs [])
=
  assert (CPI.step_output wire_outputs ([] <: list unit) ==
          ({ SM.so_wire_outputs = wire_outputs; SM.so_local_outputs = ([] <: list unit) }))

let lemma_network_noop
  (input:TCP.bytes) (input_len:SZ.t)
  (old_out:TCP.bytes) (out_len:SZ.t)
  (received0 sent0:TCP.bytes) (st0:TP.tftp_client_state)
  : Lemma
      (requires CPI.buffers_wf input input_len old_out out_len)
      (ensures
        CPI.network_process_correct TP.tftp_client_wfsm input input_len
          old_out old_out out_len
          received0 sent0 st0
          (tc_result CPI.IllegalTransition 0sz 0sz)
          received0 sent0 st0
          Seq.empty [] [])
=
  lemma_output_written_empty old_out;
  assert (WF.serialize_all tftp_wire_format ([] <: list tftp_message) == Seq.empty);
  assert (Seq.equal (Seq.append received0 (Seq.empty <: TCP.bytes)) received0);
  assert (Seq.equal (Seq.append sent0 (Seq.empty <: TCP.bytes)) sent0);
  assert (CPI.network_error_refines_state_machine TP.tftp_client_wfsm
            (CPI.input_bytes input input_len) st0 st0 Seq.empty [] [])

let lemma_local_illegal
  (ev:TP.tftp_client_local)
  (old_out out_bytes:TCP.bytes) (out_len:SZ.t)
  (received0 sent0:TCP.bytes) (st0:TP.tftp_client_state)
  : Lemma
      (requires
        SZ.v out_len == Seq.length old_out /\
        Seq.equal out_bytes old_out /\
        Seq.length out_bytes == Seq.length old_out)
      (ensures
        CPI.local_process_correct TP.tftp_client_wfsm ev old_out out_bytes out_len
          received0 sent0 st0
          (tc_result CPI.IllegalTransition 0sz 0sz)
          received0 sent0 st0
          [] [])
=
  assert (WF.serialize_all tftp_wire_format ([] <: list tftp_message) == Seq.empty);
  lemma_output_written_empty out_bytes;
  Seq.append_empty_r sent0;
  assert (CPI.local_error_refines_state_machine
    TP.tftp_client_wfsm st0 st0 [] [])
