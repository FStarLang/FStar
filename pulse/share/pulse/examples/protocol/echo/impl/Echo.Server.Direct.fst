module Echo.Server.Direct

#lang-pulse

(**
  Echo server written directly against [Pulse.Lib.BufferedTCP], scheduled by
  the Layer-1 pure classifier [Echo.Spec.echo_sp]
  ([Pulse.Lib.BufferedStream.Classifier]):

    loop:
      process the exact pending bytes ([Echo.Step.echo_step]);
      Yield    -> a frame was echoed and committed; process again;
      NeedMore -> (and only then) read more bytes ([BT.read_more]);
                  a 0-byte read means the peer closed: stop;
      Reject   -> malformed header: stop.

  This is the "process before read" discipline of Layer 1: a read is only
  performed when [needs_more echo_sp () pending] holds.
**)

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module Seq = FStar.Seq
module SZ  = FStar.SizeT
module U8  = FStar.UInt8
module U64 = FStar.UInt64
module TCP = Pulse.Lib.TCP
module BT  = Pulse.Lib.BufferedTCP

open Pulse.Lib.BufferedStream.Classifier
open Echo.Spec
open Echo.Report
open Echo.Step

(** What the caller learns when the server stops. *)
noextract
let stop_reason (st:echo_status) (pending:bytes) : prop =
  match st with
  | EchoClosed -> needs_more echo_sp () pending
  | EchoMalformed -> Reject? (classify () pending)
  | _ -> False

noextract
let serve_inv
  (committed0:bytes)
  (model:BT.phys_buffer)
  (received committed sent ob:bytes)
  : prop =
  Seq.length ob == SZ.v out_capacity /\
  echo_inv committed sent /\
  BT.buffer_wf model /\
  BT.received_split received committed model /\
  BT.capacity model >= max_frame /\
  TCP.bytes_extends committed0 committed

let lemma_extends_refl (s:bytes) : Lemma (TCP.bytes_extends s s) =
  Seq.lemma_eq_elim s (Seq.slice s 0 (Seq.length s))

let lemma_extends_trans (a b c:bytes)
  : Lemma (requires TCP.bytes_extends a b /\ TCP.bytes_extends b c)
          (ensures TCP.bytes_extends a c)
= Seq.slice_slice c 0 (Seq.length b) 0 (Seq.length a)

let lemma_can_read (model:BT.phys_buffer)
  : Lemma
      (requires
        BT.buffer_wf model /\
        BT.capacity model >= max_frame /\
        needs_more echo_sp () (BT.pending model))
      (ensures BT.can_read model)
= lemma_needmore_short (BT.pending model)

let lemma_empty_read
  (model model':BT.phys_buffer)
  (chunk:bytes)
  : Lemma
      (requires
        needs_more echo_sp () (BT.pending model) /\
        Seq.length chunk == 0 /\
        Seq.equal (BT.pending model') (Seq.append (BT.pending model) chunk))
      (ensures needs_more echo_sp () (BT.pending model'))
= Seq.lemma_eq_elim (BT.pending model') (BT.pending model)

let lemma_after_yield
  (received committed0 committed:bytes)
  (model:BT.phys_buffer)
  (committed':bytes)
  (model':BT.phys_buffer)
  : Lemma
      (requires
        stream_invariant received committed model /\
        TCP.bytes_extends committed0 committed /\
        (committed', model') == step_commit echo_sp () committed model)
      (ensures
        stream_invariant received committed' model' /\
        TCP.bytes_extends committed0 committed')
= lemma_step_commit_preserves echo_sp () received committed model;
  lemma_step_commit_extends echo_sp () committed model;
  lemma_extends_trans committed0 committed committed'

noextract inline_for_extraction
let incr_frames (n:U64.t) : U64.t =
  if U64.lt n 0xffffffffffffffffUL then U64.add n 1UL else n

#push-options "--z3rlimit 10"
divergent fn serve_direct
  (b:BT.t)
  (out:array U8.t)
  (#model:erased BT.phys_buffer)
  (#received #committed #sent:erased bytes)
  (#ob:erased bytes)
  requires
    BT.is_buffered b model received committed sent **
    pts_to out ob **
    pure (
      Seq.length ob == SZ.v out_capacity /\
      echo_inv committed sent /\
      BT.capacity model >= max_frame)
  returns r:echo_report
  ensures
    exists* model' received' committed' sent' ob'.
      BT.is_buffered b model' received' committed' sent' **
      pts_to out ob' **
      pure (
        serve_inv committed model' received' committed' sent' ob' /\
        stop_reason r.status (BT.pending model'))
{
  BT.recall_model b;
  lemma_extends_refl committed;
  let mut frames = 0UL;
  let mut go = true;
  let mut status = EchoClosed;
  while (!go)
    invariant exists* vgo vframes vstatus model1 received1 committed1 sent1 ob1.
      pts_to go vgo **
      pts_to frames vframes **
      pts_to status vstatus **
      BT.is_buffered b model1 received1 committed1 sent1 **
      pts_to out ob1 **
      pure (
        serve_inv committed model1 received1 committed1 sent1 ob1 /\
        (not vgo ==> stop_reason vstatus (BT.pending model1)))
  {
    with model1 received1 committed1 sent1 ob1.
      assert (BT.is_buffered b model1 received1 committed1 sent1 **
              pts_to out ob1);
    let d = echo_step b out;
    with model2 committed2 sent2 ob2.
      assert (BT.is_buffered b model2 received1 committed2 sent2 **
              pts_to out ob2);
    match d {
      Yield _ _ -> {
        lemma_after_yield received1 committed committed1 model1 committed2 model2;
        let n = !frames;
        frames := incr_frames n;
      }
      NeedMore -> {
        // Process-before-read: the classifier asked for more input on the
        // exact pending bytes, so a read is warranted and there is room.
        lemma_can_read model2;
        let n = BT.read_more b;
        with chunk model3.
          assert (BT.is_buffered b model3 (Seq.append received1 chunk) committed2 sent2);
        BT.recall_model b;
        if (n = 0sz) {
          lemma_empty_read model2 model3 chunk;
          go := false;
          status := EchoClosed;
        }
      }
      Reject _ -> {
        go := false;
        status := EchoMalformed;
      }
      Progress _ -> {
        // [classify] never returns Progress
        unreachable ()
      }
    }
  };
  let n = !frames;
  let st = !status;
  ({ frames = n; status = st })
}
#pop-options
