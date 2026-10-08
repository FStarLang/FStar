module TFTP.Impl.Server.Loop

(**
  A verified, **Low*-EXTRACTABLE** IETF TFTP (RFC 1350) *server* (sender) driver
  loop.

  Structural port of `YModem.Impl.Server.Loop`, adapted to the four TFTP-specific
  differences (see the module docstring there for the YMODEM shape):

    1. UNPADDED, VARIABLE-LENGTH blocks.  `TFTP.Impl.Server.Plan.block` cuts the
       file into consecutive chunks of at most 512 bytes with a SHORT final block
       (the RFC 1350 end-of-transfer marker); the loop computes each block's
       runtime length `block_len_c = min 512 (nbytes - c*512)` and identifies it
       with `Seq.length (Plan.block …)` via `Plan.block_len_eq`.

    2. DATAGRAM ACK read.  A TFTP ACK is a self-delimited 4-byte datagram, read
       with `TCP.read ch ackbuf 4sz` (NOT YMODEM's fixed `read_full`); the n-byte
       datagram is dispatched through `run_process_network` (the committed
       `CanonicalProtocol.tftp_server_process_network` leaf).

    3. INDEXED 16-bit DATA send.  Block `c` is sent as DATA #(c+1); the loop keeps
       a `blkno : U16.t` counter with `U16.v blkno == cursor + 1`, incremented
       after each ACK.  `tftp_server_send_block` frames the DATA packet
       (opcode 0x0003 ++ block# ++ payload) directly into `out` and sends exactly
       `4 + block_len_c` bytes.

    4. NO EOT.  When the cursor reaches `nblocks` (every block sent AND acked) the
       loop fires `tftp_server_complete` (status cell -> 2uy) and stops; the short
       final block is what signals completion to the receiver.

  As in the YMODEM port, the send events use Low* action wrappers
  (`tftp_server_start`, `tftp_server_send_block`, `tftp_server_complete`) whose
  event data is `Ghost.erased`: each is the corresponding
  `tftp_server_process_local` branch with the spec-carrying event replaced by
  erased ghosts and the frame bookkeeping inlined; the MonotonicGhostRef /
  ReflexiveTransitiveClosure / Log operations all erase.  The send-plan coupling
  `loop_coupling` keeps the concrete cursor in lock-step with the ghost ARQ
  state's `tss_sent`/`tss_pending` (`Plan.blocks_of` split at the cursor), so each
  `send_block` discharges `hd pending == block cursor`; after each ACK the
  coupling is re-established at `cursor+1` via `Plan.lemma_send_shift`.

  Tier-1 simplification (lossless cooperative peer): no NAK-retransmit /
  Server_timeout; completion fires directly after the final ACK.
**)

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module CPI  = Pulse.Lib.Protocol.Implementation
module SZ   = FStar.SizeT
module Seq  = FStar.Seq
module TCP  = Pulse.Lib.TCP
module U8   = FStar.UInt8
module U16  = FStar.UInt16
module Vec  = Pulse.Lib.Vec
module MR   = Pulse.Lib.MonotonicGhostRef
module RTC  = FStar.ReflexiveTransitiveClosure
module R    = Pulse.Lib.Reference
module A    = Pulse.Lib.Array
module L    = FStar.List.Tot
module FT   = Pulse.Lib.Protocol.FileTransfer
module Math = FStar.Math.Lemmas

module TP    = TFTP.Protocol
module CC    = TFTP.Impl.Server.CanonicalProtocol
module Log   = TFTP.Impl.Server.Log
module Plan  = TFTP.Impl.Server.Plan
module Codec = TFTP.Impl.Codec

open TFTP.Wire

#set-options "--fuel 2 --ifuel 2 --z3rlimit 10"

(* ───────────────────────────────────────────────────────────────────────────
   THE SEND-PLAN COUPLING.

   `loop_coupling contents nblocks filename st c` says the loop is in the
   "ready-to-send-next-block" state: nothing outstanding (acked == length sent),
   still InProgress, and the cursor `c` == the number of sent blocks, with
   `tss_sent`/`tss_pending` the low/high `blocks_of` split at `c`.
   ─────────────────────────────────────────────────────────────────────────── *)
unfold
let loop_coupling
  (contents:TCP.bytes) (nblocks:nat) (filename:TCP.bytes)
  (st:TP.tftp_server_state) (c:SZ.t) : prop =
  st.TP.tss_filename == Some filename /\
  st.TP.tss_status == FT.FT_InProgress /\
  st.TP.tss_acked == L.length st.TP.tss_sent /\
  SZ.v c == L.length st.TP.tss_sent /\
  SZ.v c <= nblocks /\
  st.TP.tss_sent == Plan.blocks_of contents 0 (L.length st.TP.tss_sent) /\
  st.TP.tss_pending == Plan.blocks_of contents (L.length st.TP.tss_sent) nblocks

(* PURE fact: none of the three network post-transitions (identity, ACK-advance,
   abort) touches `tss_sent`/`tss_pending`/`tss_filename` — they only bump
   `tss_acked` / flip `tss_status`.  So after `process_network` the send-plan
   fields carry over unchanged from the pre-state. *)
let lemma_net_post_preserves (sa st1:TP.tftp_server_state)
  : Lemma
    (requires
      st1 == sa \/ st1 == Log.ack_next_state sa \/ st1 == Log.abort_next_state sa)
    (ensures
      st1.TP.tss_sent == sa.TP.tss_sent /\
      st1.TP.tss_pending == sa.TP.tss_pending /\
      st1.TP.tss_filename == sa.TP.tss_filename)
  = ()

(* ───────────────────────────────────────────────────────────────────────────
   1.  tftp_server_start — Low* wrapper for the Server_start bootstrap.

   Models the `Server_start` branch of `tftp_server_process_local`, with the
   (filename, plan) taken ERASED (they feed only the ghost log).  Concrete
   effect: status cell stays `0uy` (idle) + the ghost log advance.  The
   precondition pins `tss_filename == None`.
   ─────────────────────────────────────────────────────────────────────────── *)
fn tftp_server_start
  (i:CC.tftp_server_impl)
  (filename:Ghost.erased TCP.bytes)
  (plan:Ghost.erased (list TCP.bytes))
  (#received #sent:Ghost.erased TCP.bytes)
  (#st:Ghost.erased TP.tftp_server_state)
requires
  CC.tftp_server_inv i received sent st **
  pure ((Ghost.reveal st).TP.tss_filename == None /\ TP.plan_wf (Ghost.reveal plan))
ensures
  CC.tftp_server_inv i received sent
    (Log.start_next_state (Ghost.reveal filename) (Ghost.reveal plan))
{
  unfold (CC.tftp_server_inv i received sent st);
  with svs evs. _;
  Log.lemma_start_step (Ghost.reveal st) (Ghost.reveal filename) (Ghost.reveal plan);
  Vec.op_Dot_Lparen_Rparen_Less_Minus i.status 0sz 0uy;
  with svs2. _;
  let log0 = Ghost.hide (Log.mk_log (Ghost.reveal received) (Ghost.reveal sent) (Ghost.reveal st));
  let log1 = Ghost.hide (Log.mk_log (Ghost.reveal received) (Ghost.reveal sent)
               (Log.start_next_state (Ghost.reveal filename) (Ghost.reveal plan)));
  Log.lemma_start_advance (Ghost.reveal received) (Ghost.reveal sent) (Ghost.reveal st)
    (Ghost.reveal filename) (Ghost.reveal plan);
  RTC.closure_step Log.ts_step_rel (Ghost.reveal log0) (Ghost.reveal log1);
  MR.update i.progress (Ghost.reveal log1);
  fold (CC.tftp_server_inv i (Ghost.reveal received) (Ghost.reveal sent)
          (Log.start_next_state (Ghost.reveal filename) (Ghost.reveal plan)));
}

(* ───────────────────────────────────────────────────────────────────────────
   2.  tftp_server_send_block — Low* wrapper for Server_send.

   Models the `Server_send` branch of `tftp_server_process_local`.  The caller
   supplies (in `data[0..data_len)`) the next block's payload `== hd pending`
   (via `local_pre_ok`); this wrapper frames the DATA packet
   `opcode(0x0003) ++ block# ++ payload` INLINE into `out` (writing the real
   bytes so the subsequent `TCP.write` sends a faithful packet), sets the status
   cell `0uy -> 1uy`, sets the `expected` cell to the block number, and advances
   the ghost log to `send_next_state st`.  The abstract payload
   `pl == Seq.slice data 0 data_len` (a `data_payload`, length <= 512) is what
   the ghost log records — the wrapper does not depend on the emitted bytes.
   ─────────────────────────────────────────────────────────────────────────── *)
fn tftp_server_send_block
  (i:CC.tftp_server_impl)
  (data:array U8.t)
  (blk:U16.t)
  (data_len:SZ.t)
  (out:array U8.t)
  (#received #sent:Ghost.erased TCP.bytes)
  (#st:Ghost.erased TP.tftp_server_state)
  (#dc #oc:Ghost.erased (Seq.seq U8.t))
requires
  CC.tftp_server_inv i received sent st **
  pts_to data dc **
  pts_to out oc **
  pure (Seq.length (Ghost.reveal dc) == 512 /\ Seq.length (Ghost.reveal oc) == 516 /\
        SZ.v data_len <= 512 /\
        CC.local_pre_ok TP.Server_send (Ghost.reveal st)
          (Seq.slice (Ghost.reveal dc) 0 (SZ.v data_len)) blk data_len)
ensures exists* (st1:TP.tftp_server_state) (nsent:TCP.bytes) (oc':Seq.seq U8.t).
  CC.tftp_server_inv i received nsent st1 **
  pts_to data dc **
  pts_to out oc' **
  pure (Seq.length oc' == 516 /\ CC.ts_local_post_ok TP.Server_send (Ghost.reveal st) st1)
{
  (* Inline DATA framing into the 516-byte out buffer: 2-byte opcode, 2-byte
     block number, then the payload.  Only the first `4 + data_len` bytes are
     ever transmitted (the caller's TCP.write cuts there). *)
  out.(0sz) <- Codec.u16_hi op_data;
  out.(1sz) <- Codec.u16_lo op_data;
  out.(2sz) <- Codec.u16_hi blk;
  out.(3sz) <- Codec.u16_lo blk;
  let mut j = 0sz;
  while (SZ.lt (!j) data_len)
  invariant exists* (vj:SZ.t) (od:Seq.seq U8.t).
    R.pts_to j vj **
    pts_to data dc **
    pts_to out od **
    pure (SZ.v vj <= SZ.v data_len /\ SZ.v data_len <= 512 /\ Seq.length od == 516)
  decreases (SZ.v data_len - SZ.v (!j))
  {
    let vj = !j;
    let dv = data.(vj);
    FStar.SizeT.fits_lte (4 + SZ.v vj) 516;
    out.(SZ.add 4sz vj) <- dv;
    j := SZ.add vj 1sz;
  };
  (* Ghost log advance (mirrors the CanonicalProtocol Server_send branch, with
     `pl` built directly from the payload slice rather than recovered from the
     emitted bytes). *)
  let pl : Ghost.erased data_payload =
    Ghost.hide (Seq.slice (Ghost.reveal dc) 0 (SZ.v data_len) <: data_payload);
  Seq.lemma_eq_elim (L.hd (Ghost.reveal st).TP.tss_pending)
                    (Seq.slice (Ghost.reveal dc) 0 (SZ.v data_len));
  unfold (CC.tftp_server_inv i received sent st);
  with svs evs. _;
  Log.lemma_send_step (Ghost.reveal st) blk (Ghost.reveal pl);
  let st1 = Ghost.hide (Log.send_next_state (Ghost.reveal st));
  let sent1 = Ghost.hide (Seq.append (Ghost.reveal sent)
                (tftp_serialize (Msg_data blk (Ghost.reveal pl))));
  Vec.op_Dot_Lparen_Rparen_Less_Minus i.status 0sz 1uy;
  with svs2. _;
  Vec.op_Dot_Lparen_Rparen_Less_Minus i.expected 0sz blk;
  with evs2. _;
  let log0 = Ghost.hide (Log.mk_log (Ghost.reveal received) (Ghost.reveal sent) (Ghost.reveal st));
  let log1 = Ghost.hide (Log.mk_log (Ghost.reveal received) (Ghost.reveal sent1) (Ghost.reveal st1));
  Log.lemma_send_advance (Ghost.reveal received) (Ghost.reveal sent) (Ghost.reveal st) blk (Ghost.reveal pl);
  RTC.closure_step Log.ts_step_rel (Ghost.reveal log0) (Ghost.reveal log1);
  MR.update i.progress (Ghost.reveal log1);
  fold (CC.tftp_server_inv i (Ghost.reveal received) (Ghost.reveal sent1) (Ghost.reveal st1));
}

(* ───────────────────────────────────────────────────────────────────────────
   3.  tftp_server_complete — Low* wrapper for Server_complete.

   Models the `Server_complete` branch.  Emits nothing; sets the status cell
   `1uy -> 2uy` (Completed), advances the ghost log to `complete_next_state st`.
   ─────────────────────────────────────────────────────────────────────────── *)
fn tftp_server_complete
  (i:CC.tftp_server_impl)
  (#received #sent:Ghost.erased TCP.bytes)
  (#st:Ghost.erased TP.tftp_server_state)
requires
  CC.tftp_server_inv i received sent st **
  pure (Some? (Ghost.reveal st).TP.tss_filename /\
        (Ghost.reveal st).TP.tss_status == FT.FT_InProgress /\
        (Ghost.reveal st).TP.tss_pending == [] /\
        (Ghost.reveal st).TP.tss_acked == L.length (Ghost.reveal st).TP.tss_sent)
ensures
  CC.tftp_server_inv i received sent (Log.complete_next_state (Ghost.reveal st))
{
  unfold (CC.tftp_server_inv i received sent st);
  with svs evs. _;
  Log.lemma_complete_step (Ghost.reveal st);
  Vec.op_Dot_Lparen_Rparen_Less_Minus i.status 0sz 2uy;
  with svs2. _;
  let log0 = Ghost.hide (Log.mk_log (Ghost.reveal received) (Ghost.reveal sent) (Ghost.reveal st));
  let log1 = Ghost.hide (Log.mk_log (Ghost.reveal received) (Ghost.reveal sent)
               (Log.complete_next_state (Ghost.reveal st)));
  Log.lemma_complete_advance (Ghost.reveal received) (Ghost.reveal sent) (Ghost.reveal st);
  RTC.closure_step Log.ts_step_rel (Ghost.reveal log0) (Ghost.reveal log1);
  MR.update i.progress (Ghost.reveal log1);
  fold (CC.tftp_server_inv i (Ghost.reveal received) (Ghost.reveal sent)
          (Log.complete_next_state (Ghost.reveal st)));
}

(* ───────────────────────────────────────────────────────────────────────────
   4.  read_server_status — read the runtime status cell, exposing the flag↔state
   agreement `ts_status_flag_ok`.  Extracts to a vector read `i->status[0]`.
   ─────────────────────────────────────────────────────────────────────────── *)
fn read_server_status
  (i:CC.tftp_server_impl)
  (#received #sent:Ghost.erased TCP.bytes)
  (#st:Ghost.erased TP.tftp_server_state)
requires
  CC.tftp_server_inv i received sent st
returns s:U8.t
ensures
  CC.tftp_server_inv i received sent st **
  pure (Log.ts_status_flag_ok s (Ghost.reveal st))
{
  unfold (CC.tftp_server_inv i received sent st);
  with svs evs. _;
  let s = Vec.op_Dot_Lparen_Rparen i.status 0sz;
  fold (CC.tftp_server_inv i received sent st);
  s
}

(* ───────────────────────────────────────────────────────────────────────────
   5.  run_process_network — first-order wrapper around the committed
   `tftp_server_process_network` leaf.  Builds the 516-byte network frame from
   the caller's scratch `tsnf`, folds the (relaxed) frame precondition,
   dispatches the ACK datagram, and unfolds the frame postcondition to hand the
   scratch back.  Exposes `ts_network_post_ok st st1` so the loop can carry the
   send-plan fields across the ACK.
   ─────────────────────────────────────────────────────────────────────────── *)
fn run_process_network
  (i:CC.tftp_server_impl)
  (tsnf:array U8.t)
  (input:array U8.t)
  (input_len:SZ.t)
  (out:array U8.t)
  (#received #sent:Ghost.erased TCP.bytes)
  (#st:Ghost.erased TP.tftp_server_state)
  (#yd #ic #oc:Ghost.erased (Seq.seq U8.t))
requires
  CC.tftp_server_inv i received sent st **
  pts_to tsnf yd **
  pts_to input ic **
  pts_to out oc **
  pure (Seq.length (Ghost.reveal yd) == 516 /\ SZ.v input_len == Seq.length (Ghost.reveal ic) /\
        Seq.length (Ghost.reveal oc) == 516)
returns result:CPI.process_result
ensures exists* (st1:TP.tftp_server_state) (received1 sent1:Ghost.erased TCP.bytes)
                (yd1 oc1:Seq.seq U8.t).
  CC.tftp_server_inv i received1 sent1 st1 **
  pts_to tsnf yd1 **
  pts_to input ic **
  pts_to out oc1 **
  pure (Seq.length yd1 == 516 /\ Seq.length oc1 == 516 /\
        CC.ts_network_post_ok (Ghost.reveal st) st1)
{
  pts_to_len out;
  let frame : CC.tftp_server_network_frame = { CC.tsnf_buf = tsnf; CC.tsnf_blk = 0us };
  rewrite (pts_to tsnf yd) as (pts_to frame.CC.tsnf_buf yd);
  fold (CC.tftp_server_network_frame_pre frame input input_len out 516sz ic oc);
  let result =
    CC.tftp_server_process_network i frame input input_len out 516sz
      received sent st ic oc;
  with received1 sent1 st1 out_contents consumed wire_outputs local_outputs. _;
  unfold (CC.tftp_server_network_frame_post
            frame result ic input_len oc out_contents (Ghost.reveal st) st1
            consumed wire_outputs local_outputs);
  with yd1. _;
  rewrite (pts_to frame.CC.tsnf_buf yd1) as (pts_to tsnf yd1);
  pts_to_len out;
  result
}

(* ───────────────────────────────────────────────────────────────────────────
   6.  copy_block_arr — dst[0..len) := src[off..off+len), through a byte loop
   (variable-length port of YMODEM's fixed 128-byte copy).  The postcondition
   exposes the copied bytes so the caller can prove `dst[0..len) == block src c`.
   ─────────────────────────────────────────────────────────────────────────── *)
fn copy_block_arr
  (src:array U8.t)
  (dst:array U8.t)
  (off:SZ.t)
  (len:SZ.t)
  (#contents:Ghost.erased TCP.bytes)
  (#d0:Ghost.erased (Seq.seq U8.t))
requires
  pts_to src contents ** pts_to dst d0 **
  pure (Seq.length (Ghost.reveal d0) == 512 /\ SZ.v len <= 512 /\
        SZ.v off + SZ.v len <= Seq.length (Ghost.reveal contents) /\
        SZ.fits (SZ.v off + SZ.v len))
returns _:unit
ensures exists* (d1:Seq.seq U8.t).
  pts_to src contents ** pts_to dst d1 **
  pure (Seq.length d1 == 512 /\ SZ.v len <= 512 /\
        SZ.v off + SZ.v len <= Seq.length (Ghost.reveal contents) /\
        (forall (k:nat). k < SZ.v len ==>
           Seq.index d1 k == Seq.index (Ghost.reveal contents) (SZ.v off + k)))
{
  let mut j = 0sz;
  while (SZ.lt (!j) len)
  invariant exists* (vj:SZ.t) (d:Seq.seq U8.t).
    R.pts_to j vj **
    pts_to src contents **
    pts_to dst d **
    pure (SZ.v vj <= SZ.v len /\ SZ.v len <= 512 /\ Seq.length d == 512 /\
          SZ.v off + SZ.v len <= Seq.length (Ghost.reveal contents) /\
          SZ.fits (SZ.v off + SZ.v len) /\
          (forall (k:nat). k < SZ.v vj ==>
             Seq.index d k == Seq.index (Ghost.reveal contents) (SZ.v off + k)))
  decreases (SZ.v len - SZ.v (!j))
  {
    let vj = !j;
    FStar.SizeT.fits_lte (SZ.v off + SZ.v vj) (SZ.v off + SZ.v len);
    let sv = src.(SZ.add off vj);
    dst.(vj) <- sv;
    j := SZ.add vj 1sz;
  };
  ()
}

(* ───────────────────────────────────────────────────────────────────────────
   7.  tftp_server_run — the verified Low* sender driver loop.

   Bounded by `fuel`; drives Server_start once, then walks the block cursor `c`,
   framing/sending DATA #(c+1) and awaiting its ACK datagram, then fires
   Server_complete once all blocks are acked (the short final block is the
   completion marker — no EOT).  Stops early on fuel exhaustion, on a
   missing/unexpected ACK, or on abort.

   The channel history (chr/chs) and the protocol history (pr/ps) are tracked
   with SEPARATE witnesses.  The send-plan coupling `loop_coupling` — held while
   `running` is true — keeps the concrete cursor in lock-step with the ghost
   `tss_sent`/`tss_pending` split, so each `send_block` discharges
   `hd pending == block cursor`.
   ─────────────────────────────────────────────────────────────────────────── *)
fn tftp_server_run
  (i:CC.tftp_server_impl)
  (ch:TCP.channel)
  (infile:array U8.t)
  (nblocks_sz:SZ.t)
  (nbytes_sz:SZ.t)
  (blk:array U8.t)
  (out:array U8.t)
  (ackbuf:array U8.t)
  (tsnf:array U8.t)
  (fuel:SZ.t)
  (#contents:Ghost.erased TCP.bytes)
  (#nblocks:Ghost.erased nat)
  (#nbytes:Ghost.erased nat)
  (#filename:Ghost.erased TCP.bytes)
requires
  TCP.is_channel ch 'r 's **
  CC.tftp_server_inv i 'r 's TP.tftp_server_initial **
  pts_to infile (Ghost.reveal contents) **
  pts_to blk 'blk ** pts_to out 'out ** pts_to ackbuf 'ackbuf ** pts_to tsnf 'tsnf **
  pure (Seq.length (Ghost.reveal contents) == Ghost.reveal nbytes /\
        SZ.v nbytes_sz == Ghost.reveal nbytes /\
        SZ.v nblocks_sz == Ghost.reveal nblocks /\
        Ghost.reveal nblocks == Ghost.reveal nbytes / 512 + 1 /\
        Ghost.reveal nblocks <= 65534 /\
        SZ.fits (Ghost.reveal nbytes) /\
        Seq.length 'blk == 512 /\ Seq.length 'out == 516 /\
        Seq.length 'ackbuf == 4 /\ Seq.length 'tsnf == 516)
returns nsent:SZ.t
ensures exists* (chr chs pr ps:TCP.bytes) (st1:TP.tftp_server_state)
                (bd od cd yd:Seq.seq U8.t).
  TCP.is_channel ch chr chs **
  CC.tftp_server_inv i pr ps st1 **
  pts_to infile (Ghost.reveal contents) **
  pts_to blk bd ** pts_to out od ** pts_to ackbuf cd ** pts_to tsnf yd **
  pure (SZ.v nsent <= Ghost.reveal nblocks)
{
  Plan.blocks_of_plan_wf (Ghost.reveal contents) 0 (Ghost.reveal nblocks);
  let plan = Ghost.hide (Plan.blocks_of (Ghost.reveal contents) 0 (Ghost.reveal nblocks));
  tftp_server_start i filename plan;
  Plan.blocks_of_empty (Ghost.reveal contents) 0 0;
  let mut remaining = fuel;
  let mut running = true;
  let mut cursor = 0sz;
  let mut blkno = 1us;
  while (
    let b = !running;
    let f = !remaining;
    b && not (f = 0sz)
  )
    invariant exists* (st:TP.tftp_server_state) (cv:SZ.t)
                      (chr chs pr ps:TCP.bytes)
                      (bd od cd yd:Seq.seq U8.t)
                      (rv:bool) (fv:SZ.t) (bn:U16.t).
      TCP.is_channel ch chr chs **
      CC.tftp_server_inv i pr ps st **
      pts_to infile (Ghost.reveal contents) **
      pts_to blk bd ** pts_to out od ** pts_to ackbuf cd ** pts_to tsnf yd **
      R.pts_to cursor cv ** R.pts_to running rv ** R.pts_to remaining fv ** R.pts_to blkno bn **
      pure (Seq.length bd == 512 /\ Seq.length od == 516 /\ Seq.length cd == 4 /\
            Seq.length yd == 516 /\ SZ.v cv <= Ghost.reveal nblocks /\
            U16.v bn == SZ.v cv + 1 /\
            (rv == true ==>
              loop_coupling (Ghost.reveal contents) (Ghost.reveal nblocks)
                (Ghost.reveal filename) st cv))
  decreases %[(if !running then 1 else 0); SZ.v (!remaining)]
  {
    with st cv. _;
    assert (pure (loop_coupling (Ghost.reveal contents) (Ghost.reveal nblocks)
                    (Ghost.reveal filename) st cv));
    let c = !cursor;
    if (SZ.lt c nblocks_sz) {
      (* c < nblocks: frame + send DATA #(c+1), then await its ACK. *)
      Plan.block_offset_le (Ghost.reveal contents) (Ghost.reveal nblocks) (SZ.v c);
      FStar.SizeT.fits_lte (SZ.v c * 512) (Ghost.reveal nbytes);
      let off = SZ.mul c 512sz;
      let rem = SZ.sub nbytes_sz off;
      let block_len_c = if (SZ.lt rem 512sz) { (rem <: SZ.t) } else { 512sz };
      Plan.block_len_eq (Ghost.reveal contents) (SZ.v c);
      Plan.block_slice (Ghost.reveal contents) (SZ.v c);
      FStar.SizeT.fits_lte (SZ.v off + SZ.v block_len_c) (Ghost.reveal nbytes);
      copy_block_arr infile blk off block_len_c;
      with bd1. _;
      (* bd1[0..block_len_c) == block contents c == hd pending (coupling discharge). *)
      assert (pure (Seq.equal (Seq.slice bd1 0 (SZ.v block_len_c))
                     (Seq.slice (Ghost.reveal contents) (SZ.v off) (SZ.v off + SZ.v block_len_c))));
      assert (pure (Seq.equal (Plan.block (Ghost.reveal contents) (SZ.v c))
                     (Seq.slice bd1 0 (SZ.v block_len_c))));
      Plan.blocks_of_unfold (Ghost.reveal contents) (SZ.v c) (Ghost.reveal nblocks);
      Plan.blocks_of_plan_wf (Ghost.reveal contents) (SZ.v c) (Ghost.reveal nblocks);
      assert (pure (Seq.equal (L.hd st.TP.tss_pending) (Seq.slice bd1 0 (SZ.v block_len_c))));
      let bn = !blkno;
      tftp_server_send_block i blk bn block_len_c out;
      with st_a nsent_a oc_a. _;
      (* st_a == send_next_state st; re-derive the shifted plan facts at c+1. *)
      Plan.lemma_send_shift (Ghost.reveal contents) (SZ.v c) (Ghost.reveal nblocks);
      FStar.List.Tot.Properties.append_length st.TP.tss_sent [L.hd st.TP.tss_pending];
      (* fits_u64-free FStar.SizeT derives `fits 516` only via fits_at_least_16's
         SMTPat, which needs `516 < pow2 16` concretized here. *)
      assert_norm (516 < pow2 16);
      FStar.SizeT.fits_lte (4 + SZ.v block_len_c) 516;
      let nw = TCP.write ch out (SZ.add 4sz block_len_c);
      let nr = TCP.read ch ackbuf 4sz;
      let res = run_process_network i tsnf ackbuf 4sz out;
      with st_b. _;
      lemma_net_post_preserves st_a st_b;
      let s = read_server_status i;
      if (s = 0uy) {
        (* ACK received: acked advanced to c+1 == length sent; coupling at c+1. *)
        assert (pure (st_b == Log.ack_next_state st_a));
        FStar.SizeT.fits_lte (SZ.v c + 1) (Ghost.reveal nblocks);
        cursor := SZ.add c 1sz;
        blkno := U16.add bn 1us;
        let f = !remaining;
        if (SZ.gt f 0sz) {
          remaining := SZ.sub f 1sz;
        } else {
          ()
        }
      } else {
        (* No ACK (block still outstanding) or abort: stop. *)
        running := false;
      }
    } else {
      (* c == nblocks: all blocks sent+acked — fire complete (no EOT). *)
      assert (pure (SZ.v c == Ghost.reveal nblocks));
      Plan.blocks_of_empty (Ghost.reveal contents) (Ghost.reveal nblocks) (Ghost.reveal nblocks);
      tftp_server_complete i;
      running := false;
    }
  };
  let final_cursor = !cursor;
  final_cursor
}
