module TFTP.Protocol

(**
  IETF TFTP (RFC 1350), read/download direction, as state-machine type-class
  instances.  Modeled as a *stop-and-wait ARQ* reliable-delivery protocol over
  the hand-written wire union `tftp_message` (`TFTP.Wire`), with per-message wire
  format the instance `TFTP.Wire.tftp_wire_format`.

  This module provides:

    * the TFTP *server* (sender) state machine, which serves a file as a sequence
      of DATA packets each carrying a 1-based block number (1, 2, 3, ...) and up
      to 512 payload bytes, advancing one block at a time as the receiver ACKs the
      block number, retransmitting the outstanding block on a timeout, and ending
      the transfer with a short (< 512-byte) final DATA block;
    * the TFTP *client* (receiver) state machine, which ACKs each DATA packet by
      block number and reassembles the file, completing on the short final block;
    * an instance of `Pulse.Lib.Protocol.FileTransfer.file_transfer` for the server, with a
      stop-and-wait window (`ft_window = Some 1`) and an INDEXED ordering
      mechanism (`FT_Data (Some i)` / `FT_Ack (Some i)`, the on-wire block
      number), exercising the exact-file reconstitution guarantee.

  ── How this differs from the YMODEM instance (its structural template) ──────

    * ORDERING IS INDEXED, not positional.  TFTP carries a real 16-bit block
      number on the wire that does NOT wrap within a transfer, so it is the
      abstract ordering mechanism: `ft_classify (Msg_data blk d) = FT_Data (Some
      (U16.v blk)) d` and `ft_classify (Msg_ack blk) = FT_Ack (Some (U16.v blk))`.
      The `ft_law_data_wire` obligation therefore ties the wire block number to
      the block's true 1-based position (`i == length blocks + 1`), and
      `ft_law_ack_wire` advances the acked prefix to the named index.  The 16-bit
      block number bounds a transfer to < 65536 blocks — exactly RFC 1350's
      inherent ~32 MB limit — enforced structurally by the `U16.t` block field.

    * UNPADDED.  A TFTP block is 0..512 bytes and the final block is short, so the
      reassembly equals the file exactly (`reassembly_exact` degenerates to a full
      equality `ft_concat blocks == content`), with no declared-length truncation.

    * NO EOT HANDSHAKE.  The short final DATA block is itself the terminator;
      there is no separate end-of-file frame or EOT phase.

    * THE START IS A LOCAL EVENT.  The client's RRQ is produced/consumed by the
      (verified, P2) codec in the impl harness, which then drives the modeled
      transfer from a local `Server_start` / `Client_start` event.  Hence RRQ/WRQ
      classify as `FT_Other` and `ft_law_request_wire` is vacuous.

    * ERROR IS MODELED IN-BAND.  An ERROR packet consumed from the wire aborts the
      transfer (`ft_classify (Msg_error _ _) = FT_Error`), directly analogous to
      YMODEM's CAN byte.
**)

module L = FStar.List.Tot
module Seq = FStar.Seq
module SP = FStar.Seq.Properties
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module SM = Pulse.Lib.Protocol.StateMachine
module WF = Pulse.Lib.Protocol.WireFormat
module WFSM = Pulse.Lib.Protocol.WireFormatStateMachine
module FT = Pulse.Lib.Protocol.FileTransfer
module TCP = Pulse.Lib.TCP

open TFTP.Wire

(* ───────────────────────────────────────────────────────────────────────────
   Block plans and reassembly lemmas
   ─────────────────────────────────────────────────────────────────────────── *)

(* Stock TFTP block size. *)
let tftp_block_size : n:nat{n >= 1} = 512

(* A "plan" is the file pre-framed into blocks, each at most 512 bytes (a real
   TFTP framing additionally makes every non-final block exactly 512 so the short
   final block terminates; the abstraction only needs the per-block bound). *)
let rec plan_wf (l:list TCP.bytes) : Tot prop (decreases l) =
  match l with
  | [] -> True
  | x :: tl -> Seq.length x <= tftp_block_size /\ plan_wf tl

(* Concatenating a block list distributes over list append. *)
let rec lemma_ft_concat_append (l1 l2:list TCP.bytes)
  : Lemma
      (ensures
        FT.ft_concat (L.append l1 l2) ==
        Seq.append (FT.ft_concat l1) (FT.ft_concat l2))
      (decreases l1)
=
  match l1 with
  | [] -> Seq.append_empty_l (FT.ft_concat l2)
  | x :: tl ->
    lemma_ft_concat_append tl l2;
    Seq.append_assoc x (FT.ft_concat tl) (FT.ft_concat l2)

(* A concatenation is a prefix of that concatenation followed by more bytes. *)
let lemma_bytes_extends_append (x y:TCP.bytes)
  : Lemma (TCP.bytes_extends x (Seq.append x y))
=
  SP.append_slices x y

(* ───────────────────────────────────────────────────────────────────────────
   Server (sender) state machine
   ─────────────────────────────────────────────────────────────────────────── *)

noeq
type tftp_server_state = {
  tss_filename : option TCP.bytes;    // file requested / being served
  tss_sent     : list TCP.bytes;      // data block payloads already sent, in order
  tss_pending  : list TCP.bytes;      // data block payloads not yet sent
  tss_acked    : nat;                 // number of leading blocks the receiver acked
  tss_status   : FT.ft_status;
}

let tftp_server_initial : tftp_server_state = {
  tss_filename = None;
  tss_sent     = [];
  tss_pending  = [];
  tss_acked    = 0;
  tss_status   = FT.FT_InProgress;
}

(* Local events driving the server:
     * Server_start   — the RRQ has been received (by the verified codec in the
       harness): the requested file name and its pre-framed blocks;
     * Server_send    — emit the next data block (stop-and-wait: only when the
       previous one is acked);
     * Server_complete— the receiver acked the final (short) block: complete;
     * Server_timeout — retransmission timeout: re-emit the outstanding block;
     * Server_abort   — cancel the transfer. *)
noeq
type tftp_server_local =
  | Server_start    : filename:TCP.bytes -> plan:list TCP.bytes -> tftp_server_local
  | Server_send     : tftp_server_local
  | Server_complete : tftp_server_local
  | Server_timeout  : tftp_server_local
  | Server_abort    : tftp_server_local

(* The raw reassembly of every data block (sent and pending): the whole file.
   Invariant under Server_send (moving the head of pending onto sent leaves the
   concatenation unchanged). *)
let tftp_full (s:tftp_server_state) : TCP.bytes =
  FT.ft_concat (L.append s.tss_sent s.tss_pending)

(* The file being served: the whole reassembly (unpadded — no truncation). *)
let tftp_content (s:tftp_server_state) : option TCP.bytes =
  match s.tss_filename with
  | None -> None
  | Some _ -> Some (tftp_full s)

(* Abstract file-transfer view of a server state. *)
let tftp_server_project (s:tftp_server_state) : FT.ft_view = {
  FT.ftv_filename    = s.tss_filename;
  FT.ftv_content     = tftp_content s;
  FT.ftv_content_len =
    (match tftp_content s with None -> None | Some c -> Some (Seq.length c));
  FT.ftv_blocks      = s.tss_sent;
  FT.ftv_acked       = s.tss_acked;
  FT.ftv_status      = s.tss_status;
}

(* The server emits the next DATA packet: it moves the head of the pending list
   onto the sent list, carrying block number = 1-based position = length sent + 1
   (the `U16.t` witness bounds the transfer to < 65536 blocks).  Stop-and-wait:
   the previous block must be acked (length sent == acked). *)
let tftp_server_send (s0 s1:tftp_server_state) (blk:U16.t) (d:data_payload) : prop =
  Some? s0.tss_filename /\
  s0.tss_status == FT.FT_InProgress /\
  L.length s0.tss_sent == s0.tss_acked /\
  U16.v blk == L.length s0.tss_sent + 1 /\
  (match s0.tss_pending with
   | [] -> False
   | h :: rest ->
     plan_wf s0.tss_pending /\
     (d <: TCP.bytes) == h /\
     s1.tss_filename == s0.tss_filename /\
     s1.tss_sent == L.append s0.tss_sent [h] /\
     s1.tss_pending == rest /\
     s1.tss_acked == s0.tss_acked /\
     s1.tss_status == FT.FT_InProgress)

(* The server retransmits the single outstanding (first unacked) data block.
   `tss_acked` (0-based) indexes it in `tss_sent`; its block number is acked+1
   (the `U16.t` witness re-establishes the < 65536 bound).  The abstract view is
   unchanged (the caller pins `s1 == s0`). *)
let tftp_retransmit_data (s0:tftp_server_state) (out:SM.step_output tftp_message unit) : prop =
  s0.tss_acked < L.length s0.tss_sent /\
  (exists (blk:U16.t) (d:data_payload).
     U16.v blk == s0.tss_acked + 1 /\
     (d <: TCP.bytes) == L.index s0.tss_sent s0.tss_acked /\
     out.SM.so_wire_outputs == [Msg_data blk d])

let tftp_server_step
  (s0:tftp_server_state)
  (ev:SM.event tftp_message tftp_server_local)
  (s1:tftp_server_state)
  (out:SM.step_output tftp_message unit)
  : GTot prop =
  match ev with
  | SM.LocalEvent (Server_start filename plan) ->
    s0.tss_filename == None /\
    plan_wf plan /\
    s1.tss_filename == Some filename /\
    s1.tss_sent == [] /\
    s1.tss_pending == plan /\
    s1.tss_acked == 0 /\
    s1.tss_status == FT.FT_InProgress /\
    out.SM.so_wire_outputs == [] /\
    out.SM.so_local_outputs == []
  | SM.LocalEvent Server_send ->
    (exists (blk:U16.t) (d:data_payload).
       tftp_server_send s0 s1 blk d /\ out.SM.so_wire_outputs == [Msg_data blk d]) /\
    out.SM.so_local_outputs == []
  | SM.LocalEvent Server_complete ->
    s0.tss_status == FT.FT_InProgress /\
    Some? s0.tss_filename /\
    s0.tss_pending == [] /\
    s0.tss_acked == L.length s0.tss_sent /\
    s1.tss_filename == s0.tss_filename /\
    s1.tss_sent == s0.tss_sent /\
    s1.tss_pending == s0.tss_pending /\
    s1.tss_acked == s0.tss_acked /\
    s1.tss_status == FT.FT_Completed /\
    out.SM.so_wire_outputs == [] /\
    out.SM.so_local_outputs == []
  | SM.LocalEvent Server_timeout ->
    s0.tss_status == FT.FT_InProgress /\
    tftp_retransmit_data s0 out /\
    s1 == s0 /\
    out.SM.so_local_outputs == []
  | SM.LocalEvent Server_abort ->
    s0.tss_status == FT.FT_InProgress /\
    s1.tss_filename == s0.tss_filename /\
    s1.tss_sent == s0.tss_sent /\
    s1.tss_pending == s0.tss_pending /\
    s1.tss_acked == s0.tss_acked /\
    s1.tss_status == FT.FT_Aborted /\
    out.SM.so_wire_outputs == [] /\
    out.SM.so_local_outputs == []
  | SM.WireEvent m ->
    (match m with
     | Msg_ack blk ->
       (* indexed data ack: the block number confirms the outstanding block *)
       s0.tss_status == FT.FT_InProgress /\
       s0.tss_acked < L.length s0.tss_sent /\
       U16.v blk == s0.tss_acked + 1 /\
       s1.tss_filename == s0.tss_filename /\
       s1.tss_sent == s0.tss_sent /\
       s1.tss_pending == s0.tss_pending /\
       s1.tss_acked == s0.tss_acked + 1 /\
       s1.tss_status == FT.FT_InProgress /\
       out.SM.so_wire_outputs == [] /\
       out.SM.so_local_outputs == []
     | Msg_error _ _ ->
       (* ERROR: abort the transfer *)
       s0.tss_status == FT.FT_InProgress /\
       s1.tss_filename == s0.tss_filename /\
       s1.tss_sent == s0.tss_sent /\
       s1.tss_pending == s0.tss_pending /\
       s1.tss_acked == s0.tss_acked /\
       s1.tss_status == FT.FT_Aborted /\
       out.SM.so_wire_outputs == [] /\
       out.SM.so_local_outputs == []
     | _ -> False)

noextract
let tftp_server_state_machine
  : SM.state_machine tftp_server_state tftp_message tftp_server_local unit =
  {
    SM.sm_initial_state = tftp_server_initial;
    SM.sm_step = tftp_server_step;
  }

noextract
let tftp_server_wfsm
  : WFSM.wire_format_state_machine tftp_server_state tftp_message tftp_server_local unit =
  {
    WFSM.wfsm_state_machine = tftp_server_state_machine;
    WFSM.wfsm_wire_format = tftp_wire_format;
  }

(* ───────────────────────────────────────────────────────────────────────────
   Client (receiver) state machine

   A valid state machine (no file_transfer instance): it ACKs each DATA packet by
   its block number, reassembles the file, completes on the short final block, and
   aborts on ERROR.
   ─────────────────────────────────────────────────────────────────────────── *)

noeq
type tftp_client_state = {
  tcs_filename : option TCP.bytes;   // file the client is receiving
  tcs_received : list TCP.bytes;     // data payloads received, in order
  tcs_status   : FT.ft_status;
}

let tftp_client_initial : tftp_client_state = {
  tcs_filename = None;
  tcs_received = [];
  tcs_status   = FT.FT_InProgress;
}

noeq
type tftp_client_local =
  | Client_start : filename:TCP.bytes -> tftp_client_local

(* The exact file the client reconstitutes: the concatenation of the received
   payloads (unpadded — the short final block ends it). *)
let tftp_client_file (s:tftp_client_state) : TCP.bytes =
  FT.ft_concat s.tcs_received

let tftp_client_step
  (s0:tftp_client_state)
  (ev:SM.event tftp_message tftp_client_local)
  (s1:tftp_client_state)
  (out:SM.step_output tftp_message unit)
  : GTot prop =
  match ev with
  | SM.LocalEvent (Client_start filename) ->
    s0.tcs_filename == None /\
    s1.tcs_filename == Some filename /\
    s1.tcs_received == [] /\
    s1.tcs_status == FT.FT_InProgress /\
    out.SM.so_wire_outputs == [] /\
    out.SM.so_local_outputs == []
  | SM.WireEvent m ->
    (match m with
     | Msg_data blk d ->
       (* receive a data block: append it and ACK the block number; a short
          block (< 512 bytes) ends the transfer *)
       Some? s0.tcs_filename /\
       s0.tcs_status == FT.FT_InProgress /\
       s1.tcs_filename == s0.tcs_filename /\
       s1.tcs_received == L.append s0.tcs_received [(d <: TCP.bytes)] /\
       (if Seq.length (d <: TCP.bytes) < tftp_block_size
        then s1.tcs_status == FT.FT_Completed
        else s1.tcs_status == FT.FT_InProgress) /\
       out.SM.so_wire_outputs == [Msg_ack blk] /\
       out.SM.so_local_outputs == []
     | Msg_error _ _ ->
       (* receive ERROR: abort *)
       Some? s0.tcs_filename /\
       s0.tcs_status == FT.FT_InProgress /\
       s1.tcs_filename == s0.tcs_filename /\
       s1.tcs_received == s0.tcs_received /\
       s1.tcs_status == FT.FT_Aborted /\
       out.SM.so_wire_outputs == [] /\
       out.SM.so_local_outputs == []
     | _ -> False)

noextract
let tftp_client_state_machine
  : SM.state_machine tftp_client_state tftp_message tftp_client_local unit =
  {
    SM.sm_initial_state = tftp_client_initial;
    SM.sm_step = tftp_client_step;
  }

noextract
let tftp_client_wfsm
  : WFSM.wire_format_state_machine tftp_client_state tftp_message tftp_client_local unit =
  {
    WFSM.wfsm_state_machine = tftp_client_state_machine;
    WFSM.wfsm_wire_format = tftp_wire_format;
  }

(* ───────────────────────────────────────────────────────────────────────────
   file_transfer instance for the server
   ─────────────────────────────────────────────────────────────────────────── *)

(* DATA = indexed data block; ACK = indexed ack; ERROR = abort; RRQ/WRQ are impl
   glue (the transfer starts from a local event), classified FT_Other. *)
let tftp_classify (m:tftp_message) : FT.ft_packet =
  match m with
  | Msg_data blk d -> FT.FT_Data (Some (U16.v blk)) (d <: TCP.bytes)
  | Msg_ack blk    -> FT.FT_Ack (Some (U16.v blk))
  | Msg_error _ _  -> FT.FT_Error
  | _              -> FT.FT_Other

(* The only retransmission timeout is Server_timeout. *)
let tftp_is_timeout (le:tftp_server_local) : bool =
  match le with
  | Server_timeout -> true
  | _ -> false

let tftp_server_law_initial (_:unit)
  : Lemma
      (ensures
        tftp_server_project tftp_server_state_machine.SM.sm_initial_state
          == FT.ft_view_empty)
=
  ()

#push-options "--fuel 2 --ifuel 2 --z3rlimit 20"

let tftp_server_law_step
  (st0:tftp_server_state)
  (ev:SM.event tftp_message tftp_server_local)
  (st1:tftp_server_state)
  (out:SM.step_output tftp_message unit)
  : Lemma
      (requires tftp_server_state_machine.SM.sm_step st0 ev st1 out)
      (ensures
        FT.ft_view_step tftp_block_size (Some 1)
          (tftp_server_project st0) (tftp_server_project st1))
=
  match ev with
  | SM.LocalEvent (Server_start filename plan) ->
    introduce exists fn ct.
      FT.ft_step_request fn ct (tftp_server_project st0) (tftp_server_project st1)
    with filename (tftp_full st1) and ()
  | SM.LocalEvent Server_send ->
    eliminate exists (blk:U16.t) (d:data_payload).
      tftp_server_send st0 st1 blk d /\ out.SM.so_wire_outputs == [Msg_data blk d]
    with
    (match st0.tss_pending with
     | [] -> ()
     | h :: rest ->
       L.append_assoc st0.tss_sent [h] rest;
       lemma_ft_concat_append (L.append st0.tss_sent [h]) rest;
       lemma_bytes_extends_append
         (FT.ft_concat (L.append st0.tss_sent [h]))
         (FT.ft_concat rest);
       FT.lemma_bytes_extends_prefix_agree
         (FT.ft_concat (L.append st0.tss_sent [h]))
         (tftp_full st1);
       introduce exists payload.
         FT.ft_step_send_data tftp_block_size (Some 1) payload
           (tftp_server_project st0) (tftp_server_project st1)
       with (d <: TCP.bytes) and ())
  | SM.LocalEvent Server_complete ->
    L.append_l_nil st0.tss_sent;
    Seq.lemma_eq_elim
      (Seq.slice (tftp_full st0) 0 (Seq.length (tftp_full st0)))
      (tftp_full st0);
    assert (FT.ft_step_complete (tftp_server_project st0) (tftp_server_project st1))
  | SM.LocalEvent Server_timeout ->
    ()
  | SM.LocalEvent Server_abort ->
    assert (FT.ft_step_error (tftp_server_project st0) (tftp_server_project st1))
  | SM.WireEvent m ->
    (match m with
     | Msg_ack blk ->
       introduce exists index.
         FT.ft_step_recv_ack index (tftp_server_project st0) (tftp_server_project st1)
       with (st0.tss_acked + 1) and ()
     | Msg_error _ _ ->
       assert (FT.ft_step_error (tftp_server_project st0) (tftp_server_project st1))
     | _ -> ())

#pop-options

#push-options "--fuel 2 --ifuel 2 --z3rlimit 20"

let tftp_server_law_data_wire
  (st0:tftp_server_state)
  (ev:SM.event tftp_message tftp_server_local)
  (st1:tftp_server_state)
  (out:SM.step_output tftp_message unit)
  (msg:tftp_message)
  : Lemma
      (requires
        tftp_server_state_machine.SM.sm_step st0 ev st1 out /\
        L.memP msg out.SM.so_wire_outputs /\
        FT.FT_Data? (tftp_classify msg))
      (ensures
        (match tftp_classify msg with
         | FT.FT_Data index payload ->
           ((match index with
             | Some i -> i == L.length (tftp_server_project st0).FT.ftv_blocks + 1
             | None -> True) /\
            (tftp_server_project st1).FT.ftv_blocks ==
              L.append (tftp_server_project st0).FT.ftv_blocks [payload])
           \/
           ((tftp_server_project st1).FT.ftv_blocks == (tftp_server_project st0).FT.ftv_blocks /\
            (match index with
             | Some i -> FT.ft_block_at (tftp_server_project st0).FT.ftv_blocks i == Some payload
             | None -> L.memP payload (tftp_server_project st0).FT.ftv_blocks))
         | _ -> True))
=
  match ev with
  | SM.LocalEvent Server_send ->
    eliminate exists (blk:U16.t) (d:data_payload).
      tftp_server_send st0 st1 blk d /\ out.SM.so_wire_outputs == [Msg_data blk d]
    with ()
  | SM.LocalEvent Server_timeout ->
    ()
  | _ -> ()

#pop-options

let tftp_server_law_ack_wire
  (st0:tftp_server_state)
  (st1:tftp_server_state)
  (out:SM.step_output tftp_message unit)
  (msg:tftp_message)
  : Lemma
      (requires
        tftp_server_state_machine.SM.sm_step st0 (SM.WireEvent msg) st1 out /\
        FT.FT_Ack? (tftp_classify msg))
      (ensures
        (match tftp_classify msg with
         | FT.FT_Ack (Some index) ->
           (tftp_server_project st0).FT.ftv_acked < index /\
           index <= L.length (tftp_server_project st0).FT.ftv_blocks /\
           (tftp_server_project st1).FT.ftv_acked == index
         | FT.FT_Ack None ->
           (tftp_server_project st0).FT.ftv_acked < L.length (tftp_server_project st0).FT.ftv_blocks /\
           (tftp_server_project st1).FT.ftv_acked == (tftp_server_project st0).FT.ftv_acked + 1
         | _ -> True))
=
  ()

let tftp_server_law_request_wire
  (st0:tftp_server_state)
  (st1:tftp_server_state)
  (out:SM.step_output tftp_message unit)
  (msg:tftp_message)
  : Lemma
      (requires
        tftp_server_state_machine.SM.sm_step st0 (SM.WireEvent msg) st1 out /\
        FT.FT_ReadRequest? (tftp_classify msg))
      (ensures
        (match tftp_classify msg with
         | FT.FT_ReadRequest filename ->
           (tftp_server_project st1).FT.ftv_filename == Some filename /\
           (tftp_server_project st1).FT.ftv_blocks == [] /\
           (tftp_server_project st1).FT.ftv_acked == 0
         | _ -> True))
=
  ()

#push-options "--fuel 2 --ifuel 2 --z3rlimit 20"

let tftp_server_law_timeout
  (st0:tftp_server_state)
  (le:tftp_server_local)
  (st1:tftp_server_state)
  (out:SM.step_output tftp_message unit)
  (msg:tftp_message)
  : Lemma
      (requires
        tftp_server_state_machine.SM.sm_step st0 (SM.LocalEvent le) st1 out /\
        tftp_is_timeout le)
      (ensures
        tftp_server_project st1 == tftp_server_project st0 /\
        (L.memP msg out.SM.so_wire_outputs /\ FT.FT_Data? (tftp_classify msg) ==>
          (match tftp_classify msg with
           | FT.FT_Data index payload ->
             (match index with
              | Some i -> FT.ft_block_at (tftp_server_project st0).FT.ftv_blocks i == Some payload
              | None -> True)
           | _ -> True)))
=
  match le with
  | Server_timeout -> ()
  | _ -> ()

#pop-options

noextract
let tftp_server_file_transfer
  : FT.file_transfer tftp_server_state tftp_message tftp_server_local unit
      tftp_server_wfsm =
  {
    FT.ft_block_size = tftp_block_size;
    FT.ft_window = Some 1;
    FT.ft_classify = tftp_classify;
    FT.ft_is_timeout = tftp_is_timeout;
    FT.ft_project = tftp_server_project;
    FT.ft_law_initial = tftp_server_law_initial;
    FT.ft_law_step = tftp_server_law_step;
    FT.ft_law_data_wire = tftp_server_law_data_wire;
    FT.ft_law_ack_wire = tftp_server_law_ack_wire;
    FT.ft_law_request_wire = tftp_server_law_request_wire;
    FT.ft_law_timeout = tftp_server_law_timeout;
  }

(* Capstone: the generic reconstitution theorem for the TFTP server.  In any
   reachable state serving a file, the raw reassembly agrees with the file on
   their common prefix, and on completion reconstitutes the exact file (here a
   full equality, since TFTP is unpadded). *)
let lemma_tftp_server_reconstitution (st:tftp_server_state)
  : Lemma
      (requires SM.valid_state tftp_server_state_machine st)
      (ensures
        (match (tftp_server_project st).FT.ftv_content with
         | None -> True
         | Some content ->
           FT.bytes_prefix_agree
             (FT.ft_concat (tftp_server_project st).FT.ftv_blocks) content /\
           ((tftp_server_project st).FT.ftv_status == FT.FT_Completed ==>
             FT.reassembly_exact (tftp_server_project st).FT.ftv_blocks content)))
=
  FT.lemma_ft_reconstitution tftp_server_file_transfer st
