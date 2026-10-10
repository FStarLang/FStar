module TFTP.Impl.Server.Log

(**
  Pure ghost-log / reachable-trace machinery for the TFTP *server* (sender)
  `Pulse.Lib.Protocol.Implementation.protocol_implementation` instance, refined
  against the reliable-delivery (stop-and-wait ARQ) spec state machine
  `TFTP.Protocol.tftp_server_wfsm`.

  This is the structural analogue of `YModem.Impl.Server.Log`, re-threaded
  through the TFTP server state type `TFTP.Protocol.tftp_server_state`.  The
  differences from the YMODEM template:

    * NO EOT phase / NO NAK.  The server consumes only two kinds of wire input:
      a 4-byte indexed DATA ACK (`Msg_ack blk`) and an ERROR datagram
      (`Msg_error code em`, which aborts).  There is no separate end-of-file
      frame; the short final DATA block is itself the terminator.

    * INDEXED ACK.  The ACK carries a 16-bit block number that must equal
      `tss_acked + 1` to advance.

    * The server state has no phase field, so the concrete status flag encodes
      only progress + whether a block is in flight:

        0uy  InProgress, nothing in flight   (tss_acked == length tss_sent)
        1uy  InProgress, one block in flight  (tss_acked + 1 == length tss_sent)
        2uy  Completed
        3uy  Aborted

  Because TFTP has NO `wire_format_stream_laws` instance (DATA is
  datagram-delimited, hence not a strong prefix parser), the reachable-trace
  invariant additionally carries `all_server_inputs_ok (trace_input_messages
  trace)` — a proof that every consumed wire message is an ACK or an ERROR, both
  of which ARE self-delimiting prefix parsers.  `lemma_server_trace_ok_valid`
  then re-derives `parses_as` from `lemma_parses_as_of_server_inputs` instead of
  the (absent) stream-law inverse.

  All of this is pure F* (no Pulse); the Pulse instance in
  `TFTP.Impl.Server.CanonicalProtocol` allocates a monotonic ghost reference
  over `ts_state_ahead_preorder` and folds `server_trace_ok` into its invariant.
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
   The sender ghost log
   ─────────────────────────────────────────────────────────────────────────── *)

noeq
type tftp_server_log = {
  tsl_received : TCP.bytes;               // all wire bytes received (ACK/ERROR datagrams)
  tsl_sent     : TCP.bytes;               // wire output bytes (emitted DATA packets)
  tsl_state    : TP.tftp_server_state;    // abstract spec state
}

(* The log is fully determined by the (received, sent, state) triple. *)
noextract
let mk_log (received sent:TCP.bytes) (st:TP.tftp_server_state) : tftp_server_log =
  { tsl_received = received; tsl_sent = sent; tsl_state = st }

(* Agreement between the concrete 1-cell status flag carried by the Pulse handle
   and the abstract state (see the module docstring for the four values). *)
noextract
let ts_status_flag_ok (s:U8.t) (st:TP.tftp_server_state) : prop =
  (s == 0uy /\ st.TP.tss_status == FT.FT_InProgress /\
     st.TP.tss_acked == L.length st.TP.tss_sent) \/
  (s == 1uy /\ st.TP.tss_status == FT.FT_InProgress /\
     st.TP.tss_acked + 1 == L.length st.TP.tss_sent) \/
  (s == 2uy /\ st.TP.tss_status == FT.FT_Completed) \/
  (s == 3uy /\ st.TP.tss_status == FT.FT_Aborted)

noextract
let server_trace =
  list (SM.transition TP.tftp_server_state tftp_message TP.tftp_server_local unit)

(* ───────────────────────────────────────────────────────────────────────────
   Generic serialize / trace list-append lemmas  (copy-verbatim from the client)
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
   Prefix-parseability of the server input sublanguage {ACK, ERROR}

   TFTP has no `wire_format_stream_laws` instance (DATA is datagram-delimited),
   but the two messages the server ever CONSUMES — a fixed 4-byte ACK and an
   ERROR (opcode + code + NUL-terminated message) — ARE self-delimiting prefix
   parsers.  These lemmas re-establish `parses_as` for any input stream drawn
   from that sublanguage, standing in for the missing stream-law inverse.
   ─────────────────────────────────────────────────────────────────────────── *)

(* dec16 inverts enc16 (needed to recover the block/code from the parsed field). *)
let lemma_dec16_enc16_id (x:U16.t) : Lemma (dec16 (enc16 x) == x)
=
  let b = enc16 x in
  E.lemma_be_to_n_is_bounded b;
  assert (E.be_to_n (enc16 x) == U16.v x);
  ()

(* ACK is a prefix parser: parsing serialize(Msg_ack blk)++rest yields
   (Msg_ack blk, rest). *)
let lemma_ack_prefix (blk:U16.t) (rest:TCP.bytes)
  : Lemma
      (tftp_parse (Seq.append (tftp_serialize (Msg_ack blk)) rest) == Some (Msg_ack blk, rest))
=
  let s = tftp_serialize (Msg_ack blk) in
  Seq.append_assoc (enc16 op_ack) (enc16 blk) rest;
  let full = Seq.append s rest in
  let mid = Seq.append (enc16 blk) rest in
  assert (Seq.equal full (Seq.append (enc16 op_ack) mid));
  SP.append_slices (enc16 op_ack) mid;
  assert (Seq.slice full 0 2 == enc16 op_ack);
  assert (E.be_to_n (Seq.slice full 0 2) == U16.v op_ack);
  SP.append_slices (enc16 blk) rest;
  lemma_dec16_enc16_id blk;
  assert (Seq.slice full 2 (Seq.length full) == mid);
  assert (Seq.slice mid 0 2 == enc16 blk);
  assert (Seq.slice mid 2 (Seq.length mid) == rest)

(* ERROR is a prefix parser (for any NUL-free message em):
   parsing serialize(Msg_error code em)++rest yields (Msg_error code em, rest). *)
let lemma_error_prefix (code:U16.t) (em:cstring) (rest:TCP.bytes)
  : Lemma
      (tftp_parse (Seq.append (tftp_serialize (Msg_error code em)) rest) ==
        Some (Msg_error code em, rest))
=
  let cn = Seq.cons 0uy Seq.empty in
  let tem = Seq.append em cn in
  let cc = Seq.append (enc16 code) tem in
  let s = tftp_serialize (Msg_error code em) in
  assert (Seq.equal s (Seq.append (enc16 op_error) cc));
  let full = Seq.append s rest in
  Seq.append_assoc (enc16 op_error) cc rest;
  let body_full = Seq.append cc rest in
  assert (Seq.equal full (Seq.append (enc16 op_error) body_full));
  SP.append_slices (enc16 op_error) body_full;
  assert (Seq.slice full 0 2 == enc16 op_error);
  assert (E.be_to_n (Seq.slice full 0 2) == U16.v op_error);
  assert (Seq.slice full 2 (Seq.length full) == body_full);
  Seq.append_assoc (enc16 code) tem rest;
  let mid2 = Seq.append tem rest in
  assert (Seq.equal body_full (Seq.append (enc16 code) mid2));
  SP.append_slices (enc16 code) mid2;
  lemma_dec16_enc16_id code;
  assert (Seq.slice body_full 0 2 == enc16 code);
  assert (Seq.slice body_full 2 (Seq.length body_full) == mid2);
  Seq.append_assoc em cn rest;
  Seq.lemma_eq_intro (Seq.append cn rest) (Seq.cons 0uy rest);
  assert (Seq.equal mid2 (Seq.append em (Seq.cons 0uy rest)));
  split_cstr_append em rest

(* The server-input sublanguage: every consumed message is an ACK or an ERROR. *)
noextract
let tftp_server_input_ok (m:tftp_message) : bool = Msg_ack? m || Msg_error? m

noextract
let rec all_server_inputs_ok (msgs:list tftp_message) : bool =
  match msgs with
  | [] -> true
  | m :: rest -> tftp_server_input_ok m && all_server_inputs_ok rest

let rec lemma_all_server_inputs_ok_append (l1 l2:list tftp_message)
  : Lemma
      (ensures
        all_server_inputs_ok (L.append l1 l2) ==
        (all_server_inputs_ok l1 && all_server_inputs_ok l2))
      (decreases l1)
=
  match l1 with
  | [] -> ()
  | m :: rest -> lemma_all_server_inputs_ok_append rest l2

(* `parses_as` for any input stream drawn from the server sublanguage (the
   stand-in for `lemma_parse_serialize_all_inverse`, which needs stream laws). *)
let rec lemma_parses_as_of_server_inputs (msgs:list tftp_message) (tail:TCP.bytes)
  : Lemma
      (requires all_server_inputs_ok msgs)
      (ensures
        WF.parses_as tftp_wire_format (WF.serialize_with_tail tftp_wire_format msgs tail) msgs tail)
      (decreases msgs)
=
  match msgs with
  | [] -> ()
  | m :: rest ->
    lemma_parses_as_of_server_inputs rest tail;
    let x = WF.serialize_with_tail tftp_wire_format rest tail in
    (match m with
     | Msg_ack blk -> lemma_ack_prefix blk x
     | Msg_error code em -> lemma_error_prefix code em x)

(* A valid WireEvent transition consumes an ACK or an ERROR (nothing else). *)
let lemma_step_wire_input_ok
  (st0 st1:TP.tftp_server_state)
  (m:tftp_message)
  (out:SM.step_output tftp_message unit)
  : Lemma
      (requires TP.tftp_server_step st0 (SM.WireEvent m) st1 out)
      (ensures tftp_server_input_ok m)
=
  ()

(* ───────────────────────────────────────────────────────────────────────────
   Single-step relation + its RTC-closure preorder
   ─────────────────────────────────────────────────────────────────────────── *)

noextract
let ts_step_body
  (log0 log1:tftp_server_log)
  (ev:SM.event tftp_message TP.tftp_server_local)
  (out:SM.step_output tftp_message unit)
  : prop =
  TP.tftp_server_step log0.tsl_state ev log1.tsl_state out /\
  Seq.equal log1.tsl_received
    (Seq.append log0.tsl_received
       (WF.serialize_all tftp_wire_format (WFSM.event_input_messages ev))) /\
  Seq.equal log1.tsl_sent
    (Seq.append log0.tsl_sent
       (WF.serialize_all tftp_wire_format out.SM.so_wire_outputs))

noextract
let ts_step_rel (log0 log1:tftp_server_log) : prop =
  exists ev out. ts_step_body log0 log1 ev out

(* Introduce a step from concrete witnesses (SMT existential intro). *)
let lemma_ts_step_rel_intro
  (log0 log1:tftp_server_log)
  (ev:SM.event tftp_message TP.tftp_server_local)
  (out:SM.step_output tftp_message unit)
  : Lemma (requires ts_step_body log0 log1 ev out) (ensures ts_step_rel log0 log1)
=
  ()

noextract
let ts_state_ahead_preorder : Pre.preorder tftp_server_log =
  RTC.closure ts_step_rel

(* ── state_ahead: a single step advances the state machine ────────────────── *)

let lemma_ts_step_state_ahead (log0 log1:tftp_server_log)
  : Lemma
      (requires ts_step_rel log0 log1)
      (ensures CPI.state_ahead TP.tftp_server_wfsm log0.tsl_state log1.tsl_state)
=
  let ev =
    ID.indefinite_description_ghost
      (SM.event tftp_message TP.tftp_server_local)
      (fun ev -> exists out. ts_step_body log0 log1 ev out) in
  let out =
    ID.indefinite_description_ghost
      (SM.step_output tftp_message unit)
      (fun out -> ts_step_body log0 log1 ev out) in
  let tr : SM.transition TP.tftp_server_state tftp_message TP.tftp_server_local unit =
    { SM.tr_event = ev; SM.tr_next_state = log1.tsl_state; SM.tr_output = out } in
  assert (SM.trace_reaches
    TP.tftp_server_wfsm.WFSM.wfsm_state_machine log0.tsl_state [tr] log1.tsl_state);
  assert (exists trace.
    SM.trace_reaches
      TP.tftp_server_wfsm.WFSM.wfsm_state_machine log0.tsl_state trace log1.tsl_state)

let lemma_ts_closure_state_ahead (log0 log1:tftp_server_log)
  : Lemma
      (requires ts_state_ahead_preorder log0 log1)
      (ensures CPI.state_ahead TP.tftp_server_wfsm log0.tsl_state log1.tsl_state)
=
  RTC.induct
    ts_step_rel
    (fun x y -> CPI.state_ahead TP.tftp_server_wfsm x.tsl_state y.tsl_state)
    (fun x ->
      SM.lemma_state_evolves_refl
        TP.tftp_server_wfsm.WFSM.wfsm_state_machine x.tsl_state)
    (fun x y -> lemma_ts_step_state_ahead x y)
    (fun x y z ->
      SM.lemma_state_evolves_trans
        TP.tftp_server_wfsm.WFSM.wfsm_state_machine x.tsl_state y.tsl_state z.tsl_state)
    log0
    log1
    ()

(* ── histories_ahead: a single step extends both byte histories ───────────── *)

let lemma_ts_step_histories_ahead (log0 log1:tftp_server_log)
  : Lemma
      (requires ts_step_rel log0 log1)
      (ensures
        TCP.bytes_extends log0.tsl_received log1.tsl_received /\
        TCP.bytes_extends log0.tsl_sent log1.tsl_sent)
=
  let ev =
    ID.indefinite_description_ghost
      (SM.event tftp_message TP.tftp_server_local)
      (fun ev -> exists out. ts_step_body log0 log1 ev out) in
  let out =
    ID.indefinite_description_ghost
      (SM.step_output tftp_message unit)
      (fun out -> ts_step_body log0 log1 ev out) in
  CPI.lemma_bytes_extends_append_equal
    log0.tsl_received log1.tsl_received
    (WF.serialize_all tftp_wire_format (WFSM.event_input_messages ev));
  CPI.lemma_bytes_extends_append_equal
    log0.tsl_sent log1.tsl_sent
    (WF.serialize_all tftp_wire_format out.SM.so_wire_outputs)

let lemma_ts_closure_histories_ahead (log0 log1:tftp_server_log)
  : Lemma
      (requires ts_state_ahead_preorder log0 log1)
      (ensures
        TCP.bytes_extends log0.tsl_received log1.tsl_received /\
        TCP.bytes_extends log0.tsl_sent log1.tsl_sent)
=
  RTC.induct
    ts_step_rel
    (fun x y ->
      TCP.bytes_extends x.tsl_received y.tsl_received /\
      TCP.bytes_extends x.tsl_sent y.tsl_sent)
    (fun x ->
      CPI.lemma_bytes_extends_refl x.tsl_received;
      CPI.lemma_bytes_extends_refl x.tsl_sent)
    (fun x y -> lemma_ts_step_histories_ahead x y)
    (fun x y z ->
      CPI.lemma_bytes_extends_trans x.tsl_received y.tsl_received z.tsl_received;
      CPI.lemma_bytes_extends_trans x.tsl_sent y.tsl_sent z.tsl_sent)
    log0
    log1
    ()

(* ───────────────────────────────────────────────────────────────────────────
   Canonical reachable-trace invariant
   ─────────────────────────────────────────────────────────────────────────── *)

noextract
let server_trace_witness
  (received sent:TCP.bytes)
  (log:tftp_server_log)
  (trace:server_trace)
  : prop =
  SM.trace_reaches
    TP.tftp_server_wfsm.WFSM.wfsm_state_machine
    TP.tftp_server_initial
    trace
    log.tsl_state /\
  Seq.equal
    received
    (WF.serialize_all tftp_wire_format (WFSM.trace_input_messages trace)) /\
  Seq.equal
    sent
    (WF.serialize_all tftp_wire_format (SM.trace_wire_outputs trace)) /\
  Seq.equal received log.tsl_received /\
  Seq.equal sent log.tsl_sent /\
  all_server_inputs_ok (WFSM.trace_input_messages trace)

noextract
let server_trace_ok
  (received sent:TCP.bytes)
  (log:tftp_server_log)
  : prop =
  exists trace. server_trace_witness received sent log trace

(* server_trace_ok refines the byte history into a valid state-machine trace.
   Since TFTP has no stream laws, `parses_as` is re-derived from the carried
   `all_server_inputs_ok` witness via `lemma_parses_as_of_server_inputs`. *)
let lemma_server_trace_ok_valid
  (received sent:TCP.bytes)
  (log:tftp_server_log)
  : Lemma
      (requires server_trace_ok received sent log)
      (ensures
        WFSM.valid_byte_trace
          TP.tftp_server_wfsm
          received
          log.tsl_state
          sent
          Seq.empty)
=
  let trace =
    ID.indefinite_description_ghost server_trace (server_trace_witness received sent log) in
  lemma_parses_as_of_server_inputs (WFSM.trace_input_messages trace) Seq.empty;
  Seq.lemma_eq_elim
    received
    (WF.serialize_all tftp_wire_format (WFSM.trace_input_messages trace));
  assert (WF.parses_as
    tftp_wire_format
    received
    (WFSM.trace_input_messages trace)
    Seq.empty);
  assert (exists trace'.
    SM.trace_reaches
      TP.tftp_server_wfsm.WFSM.wfsm_state_machine
      TP.tftp_server_wfsm.WFSM.wfsm_state_machine.SM.sm_initial_state
      trace'
      log.tsl_state /\
    WF.parses_as
      tftp_wire_format
      received
      (WFSM.trace_input_messages trace')
      Seq.empty /\
    Seq.equal
      sent
      (WF.serialize_all tftp_wire_format (SM.trace_wire_outputs trace')))

(* The freshly-created sender at the initial state: reached by the empty trace,
   so both byte histories are empty. *)
let lemma_initial_trace_ok ()
  : Lemma
      (server_trace_ok Seq.empty Seq.empty
        (mk_log Seq.empty Seq.empty TP.tftp_server_initial))
=
  let trace : server_trace = [] in
  assert (SM.trace_reaches
    TP.tftp_server_wfsm.WFSM.wfsm_state_machine
    TP.tftp_server_initial
    trace
    TP.tftp_server_initial);
  Seq.lemma_eq_elim
    Seq.empty
    (WF.serialize_all tftp_wire_format (WFSM.trace_input_messages trace));
  Seq.lemma_eq_elim
    Seq.empty
    (WF.serialize_all tftp_wire_format (SM.trace_wire_outputs trace));
  assert (server_trace_witness Seq.empty Seq.empty
    (mk_log Seq.empty Seq.empty TP.tftp_server_initial) trace)

(* ───────────────────────────────────────────────────────────────────────────
   Extending the canonical trace by one step
   ─────────────────────────────────────────────────────────────────────────── *)

let lemma_server_trace_ok_step
  (received0 sent0:TCP.bytes)
  (st0:TP.tftp_server_state)
  (ev:SM.event tftp_message TP.tftp_server_local)
  (st1:TP.tftp_server_state)
  (out:SM.step_output tftp_message unit)
  : Lemma
      (requires
        server_trace_ok received0 sent0 (mk_log received0 sent0 st0) /\
        TP.tftp_server_step st0 ev st1 out)
      (ensures
        server_trace_ok
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
    ID.indefinite_description_ghost server_trace (server_trace_witness received0 sent0 log0) in
  let tr : SM.transition TP.tftp_server_state tftp_message TP.tftp_server_local unit =
    { SM.tr_event = ev; SM.tr_next_state = st1; SM.tr_output = out } in
  assert (SM.trace_reaches TP.tftp_server_state_machine st0 [tr] st1);
  SM.lemma_trace_reaches_append
    TP.tftp_server_wfsm.WFSM.wfsm_state_machine
    TP.tftp_server_initial st0 st1 trace0 [tr];
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
  (* the new input messages are all ACK/ERROR (so the sublanguage is preserved) *)
  (match ev with
   | SM.WireEvent m -> lemma_step_wire_input_ok st0 st1 m out
   | SM.LocalEvent _ -> ());
  lemma_all_server_inputs_ok_append
    (WFSM.trace_input_messages trace0) (WFSM.event_input_messages ev);
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
  assert (server_trace_witness received1 sent1 (mk_log received1 sent1 st1) trace1)

(* ───────────────────────────────────────────────────────────────────────────
   process_result values, wire-output lists, step outputs, next-state helpers
   ─────────────────────────────────────────────────────────────────────────── *)

unfold
let ts_result (status:CPI.process_status) (consumed_len produced_len:SZ.t) : CPI.process_result =
  { CPI.process_status = status;
    CPI.process_consumed_len = consumed_len;
    CPI.process_produced_len = produced_len;
    CPI.process_app_len = 0sz }

noextract let no_wire_outputs : list tftp_message = []
noextract let data_wire_outputs (blk:U16.t) (pl:data_payload) : list tftp_message = [Msg_data blk pl]
noextract let no_local_outputs : list unit = []

noextract
let empty_output : SM.step_output tftp_message unit =
  { SM.so_wire_outputs = no_wire_outputs; SM.so_local_outputs = no_local_outputs }
noextract
let data_output (blk:U16.t) (pl:data_payload) : SM.step_output tftp_message unit =
  { SM.so_wire_outputs = data_wire_outputs blk pl; SM.so_local_outputs = no_local_outputs }

(* The started state Server_start installs (filename known, plan queued). *)
noextract
let start_next_state (filename:TCP.bytes) (plan:list TCP.bytes)
  : TP.tftp_server_state =
  { TP.tss_filename = Some filename; TP.tss_sent = [];
    TP.tss_pending = plan; TP.tss_acked = 0;
    TP.tss_status = FT.FT_InProgress }

(* Server_send moves the head of `pending` onto `sent` (stop-and-wait). *)
noextract
let send_next_state (st0:TP.tftp_server_state{Cons? st0.TP.tss_pending})
  : TP.tftp_server_state =
  { st0 with TP.tss_sent = L.append st0.TP.tss_sent [L.hd st0.TP.tss_pending];
             TP.tss_pending = L.tl st0.TP.tss_pending }

(* Server_complete: the final block was acked (only the status flips). *)
noextract
let complete_next_state (st0:TP.tftp_server_state) : TP.tftp_server_state =
  { st0 with TP.tss_status = FT.FT_Completed }

(* Server_abort / Msg_error: cancel (only the status flips). *)
noextract
let abort_next_state (st0:TP.tftp_server_state) : TP.tftp_server_state =
  { st0 with TP.tss_status = FT.FT_Aborted }

(* Msg_ack: advance the acked prefix by one (stop-and-wait window closes). *)
noextract
let ack_next_state (st0:TP.tftp_server_state) : TP.tftp_server_state =
  { st0 with TP.tss_acked = st0.TP.tss_acked + 1 }

(* ───────────────────────────────────────────────────────────────────────────
   Step-witnesses: the enabled spec transitions
   ─────────────────────────────────────────────────────────────────────────── *)

let lemma_start_step
  (st0:TP.tftp_server_state) (filename:TCP.bytes) (plan:list TCP.bytes)
  : Lemma
      (requires st0.TP.tss_filename == None /\ TP.plan_wf plan)
      (ensures
        TP.tftp_server_step st0 (SM.LocalEvent (TP.Server_start filename plan))
          (start_next_state filename plan) empty_output)
=
  ()

let lemma_send_step (st0:TP.tftp_server_state) (blk:U16.t) (pl:data_payload)
  : Lemma
      (requires
        Some? st0.TP.tss_filename /\ st0.TP.tss_status == FT.FT_InProgress /\
        L.length st0.TP.tss_sent == st0.TP.tss_acked /\
        U16.v blk == L.length st0.TP.tss_sent + 1 /\
        Cons? st0.TP.tss_pending /\ TP.plan_wf st0.TP.tss_pending /\
        (pl <: TCP.bytes) == L.hd st0.TP.tss_pending)
      (ensures
        TP.tftp_server_step st0 (SM.LocalEvent TP.Server_send)
          (send_next_state st0) (data_output blk pl))
=
  introduce exists (blk':U16.t) (d':data_payload).
    TP.tftp_server_send st0 (send_next_state st0) blk' d' /\
    (data_output blk pl).SM.so_wire_outputs == [Msg_data blk' d']
  with blk pl
  and ()

let lemma_complete_step (st0:TP.tftp_server_state)
  : Lemma
      (requires
        st0.TP.tss_status == FT.FT_InProgress /\ Some? st0.TP.tss_filename /\
        st0.TP.tss_pending == [] /\ st0.TP.tss_acked == L.length st0.TP.tss_sent)
      (ensures
        TP.tftp_server_step st0 (SM.LocalEvent TP.Server_complete)
          (complete_next_state st0) empty_output)
=
  ()

let lemma_timeout_step (st0:TP.tftp_server_state) (blk:U16.t) (pl:data_payload)
  : Lemma
      (requires
        st0.TP.tss_status == FT.FT_InProgress /\
        st0.TP.tss_acked < L.length st0.TP.tss_sent /\
        U16.v blk == st0.TP.tss_acked + 1 /\
        (pl <: TCP.bytes) == L.index st0.TP.tss_sent st0.TP.tss_acked)
      (ensures
        TP.tftp_server_step st0 (SM.LocalEvent TP.Server_timeout) st0 (data_output blk pl))
=
  introduce exists (blk':U16.t) (d':data_payload).
    U16.v blk' == st0.TP.tss_acked + 1 /\
    (d' <: TCP.bytes) == L.index st0.TP.tss_sent st0.TP.tss_acked /\
    (data_output blk pl).SM.so_wire_outputs == [Msg_data blk' d']
  with blk pl
  and ()

let lemma_abort_step (st0:TP.tftp_server_state)
  : Lemma
      (requires st0.TP.tss_status == FT.FT_InProgress)
      (ensures
        TP.tftp_server_step st0 (SM.LocalEvent TP.Server_abort)
          (abort_next_state st0) empty_output)
=
  ()

let lemma_ack_step (st0:TP.tftp_server_state) (blk:U16.t)
  : Lemma
      (requires
        st0.TP.tss_status == FT.FT_InProgress /\
        st0.TP.tss_acked < L.length st0.TP.tss_sent /\
        U16.v blk == st0.TP.tss_acked + 1)
      (ensures
        TP.tftp_server_step st0 (SM.WireEvent (Msg_ack blk))
          (ack_next_state st0) empty_output)
=
  ()

let lemma_error_step (st0:TP.tftp_server_state) (code:U16.t) (em:cstring)
  : Lemma
      (requires st0.TP.tss_status == FT.FT_InProgress)
      (ensures
        TP.tftp_server_step st0 (SM.WireEvent (Msg_error code em))
          (abort_next_state st0) empty_output)
=
  ()

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

(* If the (4+len)-byte buffer holds the serialized DATA packet, `output_written`
   holds at that produced-length. *)
let lemma_data_output_written
  (o:TCP.bytes) (produced_len:SZ.t) (blk:U16.t) (pl:data_payload)
  : Lemma
      (requires
        SZ.v produced_len == Seq.length o /\
        (o <: TCP.bytes) == tftp_serialize (Msg_data blk pl))
      (ensures
        CPI.output_written o produced_len
          (WF.serialize_all tftp_wire_format (data_wire_outputs blk pl)))
=
  lemma_tftp_serialize_all_singleton (Msg_data blk pl);
  Seq.lemma_eq_intro (CPI.output_prefix o produced_len) (tftp_serialize (Msg_data blk pl))

(* ───────────────────────────────────────────────────────────────────────────
   Message identification from an observed (length, opcode, field bytes)
   ─────────────────────────────────────────────────────────────────────────── *)

(* Forward-evaluate the parser of a 4-byte ACK datagram from its opcode bytes. *)
let lemma_ack_parse_eval (i:TCP.bytes)
  : Lemma
      (requires
        Seq.length i == 4 /\
        Seq.index i 0 == Codec.u16_hi op_ack /\
        Seq.index i 1 == Codec.u16_lo op_ack)
      (ensures
        tftp_parse i ==
          Some (Msg_ack (Codec.u16_of_bytes (Seq.index i 2) (Seq.index i 3)), Seq.empty))
=
  let blk = Codec.u16_of_bytes (Seq.index i 2) (Seq.index i 3) in
  Codec.lemma_enc16_bytes op_ack;
  Codec.lemma_u16_of_bytes (Seq.index i 2) (Seq.index i 3);
  Codec.lemma_dec16_enc16 (Seq.append (Seq.create 1 (Seq.index i 2)) (Seq.create 1 (Seq.index i 3)));
  Seq.lemma_eq_intro (tftp_serialize (Msg_ack blk)) i;
  lemma_tftp_parse_serialize_exact (Msg_ack blk)

(* A 4-byte ACK datagram equals the serialization of Msg_ack of its block. *)
let lemma_input_is_serialize_ack (i:TCP.bytes) (blk:U16.t)
  : Lemma
      (requires
        Seq.length i == 4 /\
        Seq.index i 0 == Codec.u16_hi op_ack /\
        Seq.index i 1 == Codec.u16_lo op_ack /\
        blk == Codec.u16_of_bytes (Seq.index i 2) (Seq.index i 3))
      (ensures i == tftp_serialize (Msg_ack blk))
=
  Codec.lemma_enc16_bytes op_ack;
  Codec.lemma_u16_of_bytes (Seq.index i 2) (Seq.index i 3);
  Codec.lemma_dec16_enc16 (Seq.append (Seq.create 1 (Seq.index i 2)) (Seq.create 1 (Seq.index i 3)));
  Seq.lemma_eq_intro (tftp_serialize (Msg_ack blk)) i

(* A 5-byte minimal ERROR datagram equals the serialization of Msg_error code
   (empty message).  Other opcode-5 inputs fall to the sound no-op instead. *)
let lemma_input_is_serialize_error (i:TCP.bytes) (code:U16.t)
  : Lemma
      (requires
        Seq.length i == 5 /\
        Seq.index i 0 == Codec.u16_hi op_error /\
        Seq.index i 1 == Codec.u16_lo op_error /\
        code == Codec.u16_of_bytes (Seq.index i 2) (Seq.index i 3) /\
        Seq.index i 4 == 0uy)
      (ensures i == tftp_serialize (Msg_error code (Seq.empty <: cstring)))
=
  Codec.lemma_enc16_bytes op_error;
  Codec.lemma_u16_of_bytes (Seq.index i 2) (Seq.index i 3);
  Codec.lemma_dec16_enc16 (Seq.append (Seq.create 1 (Seq.index i 2)) (Seq.create 1 (Seq.index i 3)));
  Seq.lemma_eq_intro (tftp_serialize (Msg_error code (Seq.empty <: cstring))) i

(* ───────────────────────────────────────────────────────────────────────────
   Advance lemmas: re-establish `server_trace_ok` and expose `ts_step_rel`
   ─────────────────────────────────────────────────────────────────────────── *)

(* ── wire events (grow the received history; ACK/ERROR emit nothing) ──────── *)

let lemma_ack_advance
  (received0 sent0:TCP.bytes) (st0:TP.tftp_server_state) (blk:U16.t)
  : Lemma
      (requires
        server_trace_ok received0 sent0 (mk_log received0 sent0 st0) /\
        st0.TP.tss_status == FT.FT_InProgress /\
        st0.TP.tss_acked < L.length st0.TP.tss_sent /\
        U16.v blk == st0.TP.tss_acked + 1)
      (ensures (
        let received1 = Seq.append received0 (tftp_serialize (Msg_ack blk)) in
        server_trace_ok received1 sent0 (mk_log received1 sent0 (ack_next_state st0)) /\
        ts_step_rel (mk_log received0 sent0 st0) (mk_log received1 sent0 (ack_next_state st0))))
=
  let st1 = ack_next_state st0 in
  lemma_ack_step st0 blk;
  lemma_tftp_serialize_all_singleton (Msg_ack blk);
  assert (WF.serialize_all tftp_wire_format no_wire_outputs == Seq.empty);
  lemma_server_trace_ok_step received0 sent0 st0 (SM.WireEvent (Msg_ack blk)) st1 empty_output;
  Seq.append_empty_r sent0;
  let received1 = Seq.append received0 (tftp_serialize (Msg_ack blk)) in
  lemma_ts_step_rel_intro (mk_log received0 sent0 st0) (mk_log received1 sent0 st1)
    (SM.WireEvent (Msg_ack blk)) empty_output

let lemma_error_advance
  (received0 sent0:TCP.bytes) (st0:TP.tftp_server_state) (code:U16.t)
  : Lemma
      (requires
        server_trace_ok received0 sent0 (mk_log received0 sent0 st0) /\
        st0.TP.tss_status == FT.FT_InProgress)
      (ensures (
        let received1 = Seq.append received0 (tftp_serialize (Msg_error code (Seq.empty <: cstring))) in
        server_trace_ok received1 sent0 (mk_log received1 sent0 (abort_next_state st0)) /\
        ts_step_rel (mk_log received0 sent0 st0) (mk_log received1 sent0 (abort_next_state st0))))
=
  let st1 = abort_next_state st0 in
  let em : cstring = Seq.empty in
  lemma_error_step st0 code em;
  lemma_tftp_serialize_all_singleton (Msg_error code em);
  assert (WF.serialize_all tftp_wire_format no_wire_outputs == Seq.empty);
  lemma_server_trace_ok_step received0 sent0 st0 (SM.WireEvent (Msg_error code em)) st1 empty_output;
  Seq.append_empty_r sent0;
  let received1 = Seq.append received0 (tftp_serialize (Msg_error code em)) in
  lemma_ts_step_rel_intro (mk_log received0 sent0 st0) (mk_log received1 sent0 st1)
    (SM.WireEvent (Msg_error code em)) empty_output

(* ── local events (received unchanged; sent grows only for DATA emits) ────── *)

let lemma_start_advance
  (received0 sent0:TCP.bytes) (st0:TP.tftp_server_state)
  (filename:TCP.bytes) (plan:list TCP.bytes)
  : Lemma
      (requires
        server_trace_ok received0 sent0 (mk_log received0 sent0 st0) /\
        st0.TP.tss_filename == None /\ TP.plan_wf plan)
      (ensures (
        let st1 = start_next_state filename plan in
        server_trace_ok received0 sent0 (mk_log received0 sent0 st1) /\
        ts_step_rel (mk_log received0 sent0 st0) (mk_log received0 sent0 st1)))
=
  let st1 = start_next_state filename plan in
  lemma_start_step st0 filename plan;
  assert (WF.serialize_all tftp_wire_format no_wire_outputs == Seq.empty);
  lemma_server_trace_ok_step received0 sent0 st0
    (SM.LocalEvent (TP.Server_start filename plan)) st1 empty_output;
  Seq.append_empty_r received0;
  Seq.append_empty_r sent0;
  lemma_ts_step_rel_intro (mk_log received0 sent0 st0) (mk_log received0 sent0 st1)
    (SM.LocalEvent (TP.Server_start filename plan)) empty_output

let lemma_send_advance
  (received0 sent0:TCP.bytes) (st0:TP.tftp_server_state) (blk:U16.t) (pl:data_payload)
  : Lemma
      (requires
        server_trace_ok received0 sent0 (mk_log received0 sent0 st0) /\
        Some? st0.TP.tss_filename /\ st0.TP.tss_status == FT.FT_InProgress /\
        L.length st0.TP.tss_sent == st0.TP.tss_acked /\
        U16.v blk == L.length st0.TP.tss_sent + 1 /\
        Cons? st0.TP.tss_pending /\ TP.plan_wf st0.TP.tss_pending /\
        (pl <: TCP.bytes) == L.hd st0.TP.tss_pending)
      (ensures (
        let sent1 = Seq.append sent0 (tftp_serialize (Msg_data blk pl)) in
        let st1 = send_next_state st0 in
        server_trace_ok received0 sent1 (mk_log received0 sent1 st1) /\
        ts_step_rel (mk_log received0 sent0 st0) (mk_log received0 sent1 st1)))
=
  let st1 = send_next_state st0 in
  lemma_send_step st0 blk pl;
  lemma_tftp_serialize_all_singleton (Msg_data blk pl);
  lemma_server_trace_ok_step received0 sent0 st0 (SM.LocalEvent TP.Server_send) st1 (data_output blk pl);
  Seq.append_empty_r received0;
  let sent1 = Seq.append sent0 (tftp_serialize (Msg_data blk pl)) in
  lemma_ts_step_rel_intro (mk_log received0 sent0 st0) (mk_log received0 sent1 st1)
    (SM.LocalEvent TP.Server_send) (data_output blk pl)

let lemma_complete_advance (received0 sent0:TCP.bytes) (st0:TP.tftp_server_state)
  : Lemma
      (requires
        server_trace_ok received0 sent0 (mk_log received0 sent0 st0) /\
        st0.TP.tss_status == FT.FT_InProgress /\ Some? st0.TP.tss_filename /\
        st0.TP.tss_pending == [] /\ st0.TP.tss_acked == L.length st0.TP.tss_sent)
      (ensures (
        let st1 = complete_next_state st0 in
        server_trace_ok received0 sent0 (mk_log received0 sent0 st1) /\
        ts_step_rel (mk_log received0 sent0 st0) (mk_log received0 sent0 st1)))
=
  let st1 = complete_next_state st0 in
  lemma_complete_step st0;
  assert (WF.serialize_all tftp_wire_format no_wire_outputs == Seq.empty);
  lemma_server_trace_ok_step received0 sent0 st0 (SM.LocalEvent TP.Server_complete) st1 empty_output;
  Seq.append_empty_r received0;
  Seq.append_empty_r sent0;
  lemma_ts_step_rel_intro (mk_log received0 sent0 st0) (mk_log received0 sent0 st1)
    (SM.LocalEvent TP.Server_complete) empty_output

let lemma_timeout_advance
  (received0 sent0:TCP.bytes) (st0:TP.tftp_server_state) (blk:U16.t) (pl:data_payload)
  : Lemma
      (requires
        server_trace_ok received0 sent0 (mk_log received0 sent0 st0) /\
        st0.TP.tss_status == FT.FT_InProgress /\
        st0.TP.tss_acked < L.length st0.TP.tss_sent /\
        U16.v blk == st0.TP.tss_acked + 1 /\
        (pl <: TCP.bytes) == L.index st0.TP.tss_sent st0.TP.tss_acked)
      (ensures (
        let sent1 = Seq.append sent0 (tftp_serialize (Msg_data blk pl)) in
        server_trace_ok received0 sent1 (mk_log received0 sent1 st0) /\
        ts_step_rel (mk_log received0 sent0 st0) (mk_log received0 sent1 st0)))
=
  lemma_timeout_step st0 blk pl;
  lemma_tftp_serialize_all_singleton (Msg_data blk pl);
  lemma_server_trace_ok_step received0 sent0 st0 (SM.LocalEvent TP.Server_timeout) st0 (data_output blk pl);
  Seq.append_empty_r received0;
  let sent1 = Seq.append sent0 (tftp_serialize (Msg_data blk pl)) in
  lemma_ts_step_rel_intro (mk_log received0 sent0 st0) (mk_log received0 sent1 st0)
    (SM.LocalEvent TP.Server_timeout) (data_output blk pl)

let lemma_abort_advance (received0 sent0:TCP.bytes) (st0:TP.tftp_server_state)
  : Lemma
      (requires
        server_trace_ok received0 sent0 (mk_log received0 sent0 st0) /\
        st0.TP.tss_status == FT.FT_InProgress)
      (ensures (
        let st1 = abort_next_state st0 in
        server_trace_ok received0 sent0 (mk_log received0 sent0 st1) /\
        ts_step_rel (mk_log received0 sent0 st0) (mk_log received0 sent0 st1)))
=
  let st1 = abort_next_state st0 in
  lemma_abort_step st0;
  assert (WF.serialize_all tftp_wire_format no_wire_outputs == Seq.empty);
  lemma_server_trace_ok_step received0 sent0 st0 (SM.LocalEvent TP.Server_abort) st1 empty_output;
  Seq.append_empty_r received0;
  Seq.append_empty_r sent0;
  lemma_ts_step_rel_intro (mk_log received0 sent0 st0) (mk_log received0 sent0 st1)
    (SM.LocalEvent TP.Server_abort) empty_output

(* ───────────────────────────────────────────────────────────────────────────
   Process-correctness packaging (the pure postconditions of the handlers)
   ─────────────────────────────────────────────────────────────────────────── *)

let lemma_network_stepok
  (input:TCP.bytes) (input_len:SZ.t)
  (old_out out_bytes:TCP.bytes) (out_len:SZ.t)
  (received0 sent0:TCP.bytes) (st0:TP.tftp_server_state)
  (msg:tftp_message)
  (st1:TP.tftp_server_state)
  (produced_len:SZ.t)
  (wire_outputs:list tftp_message)
  (produced:TCP.bytes)
  : Lemma
      (requires
        CPI.buffers_wf input input_len old_out out_len /\
        Seq.length out_bytes == Seq.length old_out /\
        SZ.v input_len == Seq.length input /\
        input == tftp_serialize msg /\
        TP.tftp_server_step st0 (SM.WireEvent msg) st1
          ({ SM.so_wire_outputs = wire_outputs; SM.so_local_outputs = [] }) /\
        Seq.equal produced (WF.serialize_all tftp_wire_format wire_outputs) /\
        CPI.output_written out_bytes produced_len produced)
      (ensures
        CPI.network_process_correct TP.tftp_server_wfsm
          input input_len old_out out_bytes out_len
          received0 sent0 st0
          (ts_result CPI.StepOk input_len produced_len)
          (Seq.append received0 input) (Seq.append sent0 produced) st1
          input wire_outputs [])
=
  Seq.lemma_eq_elim (CPI.input_bytes input input_len) input;
  lemma_tftp_parse_serialize_exact msg;
  Seq.append_empty_r input;
  assert (CPI.step_output wire_outputs ([] <: list unit) ==
          ({ SM.so_wire_outputs = wire_outputs; SM.so_local_outputs = ([] <: list unit) }));
  assert (CPI.consumed_by_parse
            TP.tftp_server_wfsm.WFSM.wfsm_wire_format
            (CPI.input_bytes input input_len) msg input Seq.empty);
  assert (TP.tftp_server_wfsm.WFSM.wfsm_state_machine.SM.sm_step
            st0 (SM.WireEvent msg) st1 (CPI.step_output wire_outputs []));
  let result = ts_result CPI.StepOk input_len produced_len in
  assert_norm (result.CPI.process_status == CPI.StepOk);
  assert_norm (result.CPI.process_consumed_len == input_len);
  assert_norm (result.CPI.process_produced_len == produced_len);
  introduce exists (msg':tftp_message) (residual:TCP.bytes) (produced':TCP.bytes).
    CPI.consumed_by_parse
      TP.tftp_server_wfsm.WFSM.wfsm_wire_format
      (CPI.input_bytes input input_len) msg' input residual /\
    SZ.v result.CPI.process_consumed_len == Seq.length input /\
    TP.tftp_server_wfsm.WFSM.wfsm_state_machine.SM.sm_step
      st0 (SM.WireEvent msg') st1 (CPI.step_output wire_outputs []) /\
    Seq.equal produced' (WF.serialize_all TP.tftp_server_wfsm.WFSM.wfsm_wire_format wire_outputs) /\
    CPI.output_written out_bytes result.CPI.process_produced_len produced' /\
    Seq.equal (Seq.append received0 input) (Seq.append received0 input) /\
    Seq.equal (Seq.append sent0 produced) (Seq.append sent0 produced')
  with msg Seq.empty produced
  and ();
  match result.CPI.process_status with
  | CPI.StepOk ->
    assert (CPI.network_process_correct TP.tftp_server_wfsm
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
  (ev:TP.tftp_server_local)
  (old_out out_bytes:TCP.bytes) (out_len:SZ.t)
  (received0 sent0:TCP.bytes) (st0:TP.tftp_server_state)
  (produced_len:SZ.t)
  (st1:TP.tftp_server_state)
  (wire_outputs:list tftp_message)
  (produced:TCP.bytes)
  : Lemma
      (requires
        SZ.v out_len == Seq.length old_out /\
        Seq.length out_bytes == Seq.length old_out /\
        TP.tftp_server_step st0 (SM.LocalEvent ev) st1
          ({ SM.so_wire_outputs = wire_outputs; SM.so_local_outputs = [] }) /\
        Seq.equal produced (WF.serialize_all tftp_wire_format wire_outputs) /\
        CPI.output_written out_bytes produced_len produced)
      (ensures
        CPI.local_process_correct TP.tftp_server_wfsm ev old_out out_bytes out_len
          received0 sent0 st0
          (ts_result CPI.StepOk 0sz produced_len)
          received0
          (Seq.append sent0 produced)
          st1 wire_outputs [])
=
  assert (CPI.step_output wire_outputs ([] <: list unit) ==
          ({ SM.so_wire_outputs = wire_outputs; SM.so_local_outputs = ([] <: list unit) }))

let lemma_network_noop
  (input:TCP.bytes) (input_len:SZ.t)
  (old_out:TCP.bytes) (out_len:SZ.t)
  (received0 sent0:TCP.bytes) (st0:TP.tftp_server_state)
  : Lemma
      (requires CPI.buffers_wf input input_len old_out out_len)
      (ensures
        CPI.network_process_correct TP.tftp_server_wfsm input input_len
          old_out old_out out_len
          received0 sent0 st0
          (ts_result CPI.IllegalTransition 0sz 0sz)
          received0 sent0 st0
          Seq.empty [] [])
=
  lemma_output_written_empty old_out;
  assert (WF.serialize_all tftp_wire_format ([] <: list tftp_message) == Seq.empty);
  assert (Seq.equal (Seq.append received0 (Seq.empty <: TCP.bytes)) received0);
  assert (Seq.equal (Seq.append sent0 (Seq.empty <: TCP.bytes)) sent0);
  assert (CPI.network_error_refines_state_machine TP.tftp_server_wfsm
            (CPI.input_bytes input input_len) st0 st0 Seq.empty [] [])

let lemma_local_illegal
  (ev:TP.tftp_server_local)
  (old_out out_bytes:TCP.bytes) (out_len:SZ.t)
  (received0 sent0:TCP.bytes) (st0:TP.tftp_server_state)
  : Lemma
      (requires
        SZ.v out_len == Seq.length old_out /\
        Seq.equal out_bytes old_out /\
        Seq.length out_bytes == Seq.length old_out)
      (ensures
        CPI.local_process_correct TP.tftp_server_wfsm ev old_out out_bytes out_len
          received0 sent0 st0
          (ts_result CPI.IllegalTransition 0sz 0sz)
          received0 sent0 st0
          [] [])
=
  assert (WF.serialize_all tftp_wire_format ([] <: list tftp_message) == Seq.empty);
  lemma_output_written_empty out_bytes;
  Seq.append_empty_r sent0;
  assert (CPI.local_error_refines_state_machine
    TP.tftp_server_wfsm st0 st0 [] [])
