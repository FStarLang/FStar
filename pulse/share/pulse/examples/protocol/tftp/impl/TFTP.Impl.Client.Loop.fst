module TFTP.Impl.Client.Loop

(**
  A verified, **Low*-EXTRACTABLE** IETF TFTP (RFC 1350) *client* (receiver)
  driver loop, ported from `YModem.Impl.Client.Loop.ymodem_client_run`.

  Like its YMODEM template, this module contains a bespoke, first-order Pulse
  loop that DIRECTLY reuses the committed verified leaf
  `TFTP.Impl.Client.CanonicalProtocol.tftp_client_process_network`.  Every step
  of the runnable C loop is verified: the datagram read, the `process_network`
  dispatch, the ACK write-back, and the payload reconstruction into a
  caller-provided buffer.

  ── How this differs from the YMODEM receiver loop ──────────────────────────

    1. DATAGRAM READ.  TFTP messages are datagram-delimited, so one UDP-style
       datagram is read PER iteration with `TCP.read ch inbuf 516sz`, which
       returns `n` = the whole datagram length (`n <= 516`).  There is NO
       YMODEM-style lead-byte-then-fixed-tail `read_full` framing.  Because
       `tftp_client_process_network`'s frame precondition pins
       `input_len == length input_contents`, the loop hands it a length-`n`
       SUB-ARRAY view of the fixed 516-byte `inbuf` (via `to_mask` / `AC.sub` /
       `from_mask`, exactly the framing used by `array_blit`), then returns the
       view with `AC.return_sub`.  The handler itself checks `opcode == DATA` and
       `4 <= n <= 516`, extracts the (ghost) payload, and emits a 4-byte ACK;
       for ERROR it aborts; else it is a sound `IllegalTransition` no-op.

    2. VARIABLE-LENGTH payload reconstruction.  A DATA block carries `n - 4`
       payload bytes (0..512), NOT a fixed 128.  `maybe_copy_payload` copies the
       `n - 4` payload bytes — which physically live at `inbuf[4 .. n)`, the
       "ghost slice of the datagram" the handler models — into `outbuf` at the
       running cursor with the `array_blit` (`memcpy_l`) helper and a RUNTIME
       length, guarding against `outbuf` overflow.  It uses the produced ACK
       length as the DATA discriminator (`process_produced_len == 4`).

    3. ACK is 4 bytes.  `maybe_write_ack` sends 4 bytes iff the handler produced
       one (`process_produced_len == 4`; 0 for ERROR / noop).

    4. Status stop values: `2uy` Completed, `3uy` Aborted (same shape as
       YMODEM's).  `tftp_client_start` flips `0uy -> 1uy` (`Client_start`).

  The channel history and the protocol (ghost) history are tracked with SEPARATE
  witnesses, exactly as in YMODEM: an unrecognized/finished frame is consumed
  from the wire (advancing the channel history) yet is a sound protocol no-op
  (leaving the protocol history unchanged).

  EXTRACTS to clean Low* C via KaRaMeL (the impl handle erases to just the
  status-byte pointer; the ghost MonotonicGhostRef vanishes).
**)

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module CPI  = Pulse.Lib.Protocol.Implementation
module SZ   = FStar.SizeT
module Seq  = FStar.Seq
module TCP  = Pulse.Lib.TCP
module U8   = FStar.UInt8
module Vec  = Pulse.Lib.Vec
module MR   = Pulse.Lib.MonotonicGhostRef
module RTC  = FStar.ReflexiveTransitiveClosure
module R    = Pulse.Lib.Reference
module A    = Pulse.Lib.Array
module AC   = Pulse.Lib.Array.Core

module TP   = TFTP.Protocol
module CC   = TFTP.Impl.Client.CanonicalProtocol
module Log  = TFTP.Impl.Client.Log

#set-options "--fuel 1 --ifuel 1 --z3rlimit 20"

(* ───────────────────────────────────────────────────────────────────────────
   1.  tftp_client_start — a Low* wrapper for the Client_start bootstrap.

   Its concrete effect is PURELY the status flip 0uy -> 1uy; the filename only
   feeds the GHOST state, so it is taken ERASED.  Modelled on the `Client_start`
   branch of `tftp_client_process_local`.  Since the precondition pins
   `tcs_filename == None`, `tc_status_flag_ok` forces the runtime status cell to
   `0uy`, so the `else` branch is dead (`unreachable`).

   EXTRACTS to roughly `void tftp_client_start(uint8_t *i){ if(i[0]==0) i[0]=1; }`.
   ─────────────────────────────────────────────────────────────────────────── *)

fn tftp_client_start
  (i:CC.tftp_client_impl)
  (filename:Ghost.erased TCP.bytes)
  (received sent:Ghost.erased TCP.bytes)
  (st:Ghost.erased TP.tftp_client_state)
requires
  CC.tftp_client_inv i received sent st **
  pure ((Ghost.reveal st).TP.tcs_filename == None)
ensures
  CC.tftp_client_inv i received sent (Log.start_next_state (Ghost.reveal filename))
{
  unfold (CC.tftp_client_inv i received sent st);
  with svs. _;
  let s = Vec.op_Dot_Lparen_Rparen i.CC.status 0sz;
  if (s = 0uy) {
    Vec.op_Dot_Lparen_Rparen_Less_Minus i.CC.status 0sz 1uy;
    with svs2. _;
    Log.lemma_start_advance
      (Ghost.reveal received) (Ghost.reveal sent) (Ghost.reveal st)
      (Ghost.reveal filename);
    RTC.closure_step Log.tc_step_rel
      (Log.mk_log (Ghost.reveal received) (Ghost.reveal sent) (Ghost.reveal st))
      (Log.mk_log (Ghost.reveal received) (Ghost.reveal sent)
        (Log.start_next_state (Ghost.reveal filename)));
    MR.update i.CC.progress
      (Log.mk_log (Ghost.reveal received) (Ghost.reveal sent)
        (Log.start_next_state (Ghost.reveal filename)));
    fold (CC.tftp_client_inv i received sent
      (Log.start_next_state (Ghost.reveal filename)));
  } else {
    unreachable ()
  }
}

(* ───────────────────────────────────────────────────────────────────────────
   2a.  run_process_network — a first-order wrapper around the committed
   `tftp_client_process_network` leaf.  Builds the single-field network frame
   from the caller's 512-byte scratch, folds the frame precondition, dispatches,
   and unfolds the frame postcondition to hand the scratch buffer back.  The
   `input` array is the length-`input_len` datagram VIEW threaded in by the
   loop; the 4-byte `ackout` receives the produced ACK.  Extracts to a direct
   `process_network` call.
   ─────────────────────────────────────────────────────────────────────────── *)

fn run_process_network
  (i:CC.tftp_client_impl)
  (scratch:array U8.t)
  (input:array U8.t)
  (input_len:SZ.t)
  (ackout:array U8.t)
  (#received #sent:Ghost.erased TCP.bytes)
  (#st:Ghost.erased TP.tftp_client_state)
  (#sc #ic #ac:Ghost.erased (Seq.seq U8.t))
requires
  CC.tftp_client_inv i received sent st **
  pts_to scratch sc **
  pts_to input ic **
  pts_to ackout ac **
  pure (Seq.length sc == 512 /\ SZ.v input_len == Seq.length ic /\ Seq.length ac == 4)
returns result:CPI.process_result
ensures exists* (received1:Ghost.erased TCP.bytes) (sent1:Ghost.erased TCP.bytes)
                (st1:Ghost.erased TP.tftp_client_state) (sc1 ac1:Seq.seq U8.t).
  CC.tftp_client_inv i received1 sent1 st1 **
  pts_to scratch sc1 **
  pts_to input ic **
  pts_to ackout ac1 **
  pure (Seq.length sc1 == 512 /\ Seq.length ac1 == 4)
{
  let frame : CC.tftp_client_network_frame = { CC.tcnf_buf = scratch };
  rewrite (pts_to scratch sc) as (pts_to frame.CC.tcnf_buf sc);
  fold (CC.tftp_client_network_frame_pre frame input input_len ackout 4sz ic ac);
  let result =
    CC.tftp_client_process_network i frame input input_len ackout 4sz
      received sent st ic ac;
  with received1 sent1 st1 out_contents consumed wire_outputs local_outputs. _;
  unfold (CC.tftp_client_network_frame_post
            frame result ic input_len ac out_contents st st1
            consumed wire_outputs local_outputs);
  with sc1. _;
  rewrite (pts_to frame.CC.tcnf_buf sc1) as (pts_to scratch sc1);
  result
}

(* ───────────────────────────────────────────────────────────────────────────
   2b.  array_blit — copy `src[src_off..src_off+n)` into `dst[dst_off..dst_off+n)`
   through concrete sub-array views (`to_mask`/`sub`/`from_mask`/`memcpy_l`/
   `return_sub`), a source-offset generalization of the YMODEM `array_blit`.
   Extracts to a `memcpy(dst + dst_off, src + src_off, n)`.  Buffer contents are
   existentially quantified in the postcondition (only lengths are pinned) — the
   loop tracks buffer contents existentially anyway.
   ─────────────────────────────────────────────────────────────────────────── *)

fn array_blit
  (dst:array U8.t) (dst_off:SZ.t) (src:array U8.t) (src_off:SZ.t) (n:SZ.t)
  (#dc #sc:Ghost.erased (Seq.seq U8.t))
requires
  pts_to dst dc ** pts_to src sc **
  pure (SZ.v dst_off + SZ.v n <= Seq.length dc /\ SZ.v src_off + SZ.v n <= Seq.length sc)
returns _:unit
ensures exists* (dc' sc':Seq.seq U8.t).
  pts_to dst dc' ** pts_to src sc' **
  pure (Seq.length dc' == Seq.length dc /\ Seq.length sc' == Seq.length sc)
{
  pts_to_len dst;
  pts_to_len src;
  to_mask src;
  let ssub = AC.sub src src_off (SZ.v src_off + SZ.v n);
  from_mask ssub;
  pts_to_len ssub;
  to_mask dst;
  let dsub = AC.sub dst dst_off (SZ.v dst_off + SZ.v n);
  from_mask dsub;
  pts_to_len dsub;
  let _sq = A.memcpy_l n ssub dsub;
  to_mask dsub;
  AC.return_sub dst;
  from_mask dst;
  to_mask ssub;
  AC.return_sub src;
  from_mask src;
  ()
}

(* ───────────────────────────────────────────────────────────────────────────
   2c.  maybe_write_ack — send the 4-byte ACK iff `process_network` produced one
   (`process_produced_len == 4`).  The channel's sent-history advances in the
   write branch and is unchanged otherwise; the explicit `exists*` post joins
   both cases.
   ─────────────────────────────────────────────────────────────────────────── *)

fn maybe_write_ack
  (ch:TCP.channel)
  (ackout:array U8.t)
  (produced_len:SZ.t)
  (#received #sent:Ghost.erased TCP.bytes)
  (#ac:Ghost.erased (Seq.seq U8.t))
requires
  TCP.is_channel ch received sent **
  pts_to ackout ac **
  pure (Seq.length ac == 4)
returns _:unit
ensures exists* (sent1:TCP.bytes).
  TCP.is_channel ch received sent1 **
  pts_to ackout ac
{
  if (produced_len = 4sz) {
    let n = TCP.write ch ackout 4sz;
    ()
  } else {
    ()
  }
}

(* ───────────────────────────────────────────────────────────────────────────
   2d.  maybe_copy_payload — after a DATA step, append the `n - 4` payload bytes
   (sitting at `datagram[4 .. n)`) to the running reconstruction `outbuf` at
   `cursor`, advancing the cursor.  DATA is discriminated by the produced ACK
   length (`produced_len == 4`).  If the payload would overflow `outcap`, stop
   the loop by clearing `running`.
   ─────────────────────────────────────────────────────────────────────────── *)

fn maybe_copy_payload
  (datagram:array U8.t)
  (outbuf:array U8.t)
  (cursor:R.ref SZ.t)
  (running:R.ref bool)
  (outcap:SZ.t)
  (n:SZ.t)
  (produced_len:SZ.t)
  (#dg #ob:Ghost.erased (Seq.seq U8.t))
  (#cv0:Ghost.erased SZ.t)
  (#rn0:Ghost.erased bool)
requires
  pts_to datagram dg **
  pts_to outbuf ob **
  R.pts_to cursor cv0 **
  R.pts_to running rn0 **
  pure (Seq.length dg == 516 /\ Seq.length ob == SZ.v outcap /\
        SZ.v n <= 516 /\ SZ.v (Ghost.reveal cv0) <= SZ.v outcap)
returns _:unit
ensures exists* (dg1 ob1:Seq.seq U8.t) (cv1:SZ.t) (rn1:bool).
  pts_to datagram dg1 **
  pts_to outbuf ob1 **
  R.pts_to cursor cv1 **
  R.pts_to running rn1 **
  pure (Seq.length dg1 == 516 /\ Seq.length ob1 == SZ.v outcap /\ SZ.v cv1 <= SZ.v outcap)
{
  if (produced_len = 4sz && SZ.gte n 4sz) {
    let payload_len = SZ.sub n 4sz;
    let cv = R.read cursor;
    let room = SZ.sub outcap cv;
    if (SZ.gte room payload_len) {
      array_blit outbuf cv datagram 4sz payload_len;
      let ncv = SZ.add cv payload_len;
      R.write cursor ncv;
    } else {
      R.write running false;
    }
  } else {
    ()
  }
}

(* ───────────────────────────────────────────────────────────────────────────
   2e.  read_status_update — read the runtime status cell and either stop the
   loop (status `2uy` Completed / `3uy` Aborted) or consume one unit of fuel.
   ─────────────────────────────────────────────────────────────────────────── *)

fn read_status_update
  (i:CC.tftp_client_impl)
  (running:R.ref bool)
  (remaining:R.ref SZ.t)
  (#received #sent:Ghost.erased TCP.bytes)
  (#st:Ghost.erased TP.tftp_client_state)
  (#rn0:Ghost.erased bool)
  (#f0:Ghost.erased SZ.t)
requires
  CC.tftp_client_inv i received sent st **
  R.pts_to running rn0 **
  R.pts_to remaining f0 **
  pure (not (Ghost.reveal f0 = 0sz))
returns _:unit
ensures exists* (rn1:bool) (f1:SZ.t).
  CC.tftp_client_inv i received sent st **
  R.pts_to running rn1 **
  R.pts_to remaining f1 **
  pure (rn1 == false \/ (rn1 == Ghost.reveal rn0 /\ SZ.v f1 < SZ.v (Ghost.reveal f0)))
{
  unfold (CC.tftp_client_inv i received sent st);
  with svs. _;
  let sv = Vec.op_Dot_Lparen_Rparen i.CC.status 0sz;
  fold (CC.tftp_client_inv i received sent st);
  if (sv = 2uy || sv = 3uy) {
    R.write running false;
  } else {
    let f = R.read remaining;
    if (SZ.gt f 0sz) {
      R.write remaining (SZ.sub f 1sz);
    } else {
      ()
    }
  }
}

(* ───────────────────────────────────────────────────────────────────────────
   3.  tftp_client_run — the verified Low* receiver driver loop.

   Bounded by `fuel`; also stops as soon as the status cell reaches `2uy`
   (Completed) or `3uy` (Aborted), or the reconstruction buffer `outbuf` fills.
   Each iteration reads one datagram, dispatches it (as a length-`n` sub-array
   view of `inbuf`) through the committed `tftp_client_process_network` leaf,
   writes back an ACK when one is produced, and (for a DATA block) appends the
   `n - 4` payload bytes to `outbuf` at the running cursor.

   Structural mirror of `YModem.Impl.Client.Loop.ymodem_client_run`.
   ─────────────────────────────────────────────────────────────────────────── *)

fn tftp_client_run
  (i:CC.tftp_client_impl)
  (ch:TCP.channel)
  (inbuf:array U8.t) (scratch:array U8.t) (ackout:array U8.t)
  (outbuf:array U8.t) (outcap:SZ.t)
  (fuel:SZ.t)
requires
  TCP.is_channel ch 'r 's **
  CC.tftp_client_inv i 'r 's 'st **
  pts_to inbuf 'ib ** pts_to scratch 'sc ** pts_to ackout 'ac ** pts_to outbuf 'ob **
  pure (Seq.length 'ib == 516 /\ Seq.length 'sc == 512 /\ Seq.length 'ac == 4 /\
        Seq.length 'ob == SZ.v outcap)
returns nbytes:SZ.t
ensures exists* (chr chs pr ps:TCP.bytes) (st1:TP.tftp_client_state)
                (ib sc ac ob:Seq.seq U8.t).
  TCP.is_channel ch chr chs **
  CC.tftp_client_inv i pr ps st1 **
  pts_to inbuf ib ** pts_to scratch sc ** pts_to ackout ac ** pts_to outbuf ob **
  pure (SZ.v nbytes <= SZ.v outcap)
{
  let mut remaining = fuel;
  let mut running = true;
  let mut cursor = 0sz;
  while (
    let b = !running;
    let rem = !remaining;
    b && not (rem = 0sz)
  )
    invariant live running
    invariant live remaining
    invariant exists* (chr chs pr ps:TCP.bytes) (st:TP.tftp_client_state)
                      (ib sc ac ob:Seq.seq U8.t) (cv:SZ.t).
      TCP.is_channel ch chr chs **
      CC.tftp_client_inv i pr ps st **
      pts_to inbuf ib ** pts_to scratch sc ** pts_to ackout ac ** pts_to outbuf ob **
      R.pts_to cursor cv **
      pure (Seq.length ib == 516 /\ Seq.length sc == 512 /\ Seq.length ac == 4 /\
            Seq.length ob == SZ.v outcap /\ SZ.v cv <= SZ.v outcap)
  decreases %[(if !running then 1 else 0); SZ.v (!remaining)]
  {
    (* read one whole datagram (n = its length, n <= 516) *)
    let n = TCP.read ch inbuf 516sz;
    (* form the length-n datagram view inbuf[0..n) and dispatch it *)
    pts_to_len inbuf;
    to_mask inbuf;
    let inp = AC.sub inbuf 0sz (SZ.v n);
    from_mask inp;
    let result = run_process_network i scratch inp n ackout;
    to_mask inp;
    AC.return_sub inbuf;
    from_mask inbuf;
    (* write back the ACK (if DATA), then append the DATA payload (if any) *)
    maybe_write_ack ch ackout result.CPI.process_produced_len;
    maybe_copy_payload inbuf outbuf cursor running outcap n result.CPI.process_produced_len;
    read_status_update i running remaining;
  };
  let final_cursor = !cursor;
  final_cursor
}
