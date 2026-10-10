module Echo.Step

#lang-pulse

(**
  One step of the echo server over a [Pulse.Lib.BufferedTCP] receive buffer:

    1. borrow the pending bytes ([BT.borrow_pending]);
    2. classify them with a concrete classifier proved equal to the pure
       [Echo.Spec.classify] (the [stream_processor] of Layer 1);
    3. on a complete frame, copy it to an output array, release the view
       ([BT.release_pending]), write the frame back ([BT.write]) and commit
       exactly the frame's bytes ([BT.commit_prefix], which compacts the
       buffer with [Pulse.Lib.Memmove]);
    4. otherwise release the view and leave the buffer unchanged.

  The step preserves [Echo.Spec.echo_inv]: sent == committed, and committed
  is a sequence of well-formed frames.
**)

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module Seq = FStar.Seq
module SZ  = FStar.SizeT
module U8  = FStar.UInt8
module TCP = Pulse.Lib.TCP
module BT  = Pulse.Lib.BufferedTCP
module A   = Pulse.Lib.Array
module Cast = FStar.Int.Cast

open Pulse.Lib.BufferedStream.Classifier
open Echo.Spec

(** Capacity of the output (echo) buffer: one maximal frame. *)
inline_for_extraction
let out_capacity : SZ.t = 258sz

let lemma_out_capacity () : Lemma (SZ.v out_capacity == max_frame) = ()

(** Receive-buffer capacity used by the servers. Any value [>= max_frame]
    works; it is deliberately small so that the C test exercises reads that
    fill the buffer and compaction of a partially consumed buffer. *)
inline_for_extraction
let recv_capacity : SZ.t = 300sz

inline_for_extraction
let u8_to_sz (b:U8.t) : r:SZ.t{SZ.v r == U8.v b} =
  SZ.uint16_to_sizet (Cast.uint8_to_uint16 b)

(* ------------------------------------------------------------------ *)
(* Concrete classifier                                                *)
(* ------------------------------------------------------------------ *)

fn classify_pending
  (data:array U8.t)
  (len:SZ.t)
  (#p:perm)
  (#s:erased bytes)
  requires pts_to data #p s ** pure (Seq.length s == SZ.v len)
  returns c:classification SZ.t echo_error
  ensures pts_to data #p s ** pure (c == classify () s)
{
  pts_to_len data;
  if (SZ.lt len 2sz) {
    NeedMore
  } else {
    let b0 = data.(0sz);
    let b1 = data.(1sz);
    let l = SZ.add (SZ.mul (u8_to_sz b0) 256sz) (u8_to_sz b1);
    assert (pure (SZ.v l == payload_len s));
    if (l = 0sz || SZ.gt l 256sz) {
      Reject Malformed
    } else {
      let k = SZ.add 2sz l;
      if (SZ.lt len k) {
        NeedMore
      } else {
        Yield k l
      }
    }
  }
}

(* ------------------------------------------------------------------ *)
(* One echo step                                                      *)
(* ------------------------------------------------------------------ *)

(** Relation between the buffer state before and after a step: the decision
    is the Layer-1 classifier's decision on the exact pending bytes; a
    complete frame is committed exactly as the generic Layer-1 scheduler step
    [step_commit] prescribes, and any other decision leaves the buffer
    untouched. *)
noextract
let step_post
  (d:classification SZ.t echo_error)
  (model:BT.phys_buffer)
  (committed:bytes)
  (model':BT.phys_buffer)
  (committed':bytes)
  : prop =
  d == echo_sp.sp_classify () (BT.pending model) /\
  (match d with
   | Yield k _ ->
     SZ.v k <= Seq.length (BT.pending model) /\
     (committed', model') == step_commit echo_sp () committed model
   | _ ->
     committed' == committed /\ model' == model)

let lemma_frame_of_yield
  (model:BT.phys_buffer)
  (ob:bytes)
  (k:SZ.t)
  (l:SZ.t)
  : Lemma
      (requires
        classify () (BT.pending model) == Yield k l /\
        SZ.v k <= Seq.length ob /\
        Seq.equal (Seq.slice ob 0 (SZ.v k))
                  (Seq.slice (BT.pending model) 0 (SZ.v k)))
      (ensures
        SZ.v k <= Seq.length (BT.pending model) /\
        is_frame (Seq.slice ob 0 (SZ.v k)) /\
        Seq.slice ob 0 (SZ.v k) == BT.take (BT.pending model) (SZ.v k))
= lemma_yield_is_frame (BT.pending model);
  Seq.lemma_eq_elim (Seq.slice ob 0 (SZ.v k))
                    (Seq.slice (BT.pending model) 0 (SZ.v k))

#push-options "--z3rlimit 10"
fn echo_step
  (b:BT.t)
  (out:array U8.t)
  (#model:erased BT.phys_buffer)
  (#received #committed #sent:erased bytes)
  (#ob:erased bytes)
  requires
    BT.is_buffered b model received committed sent **
    pts_to out ob **
    pure (Seq.length ob == SZ.v out_capacity /\ echo_inv committed sent)
  returns d:classification SZ.t echo_error
  ensures
    exists* model' committed' sent' ob'.
      BT.is_buffered b model' received committed' sent' **
      pts_to out ob' **
      pure (
        Seq.length ob' == SZ.v out_capacity /\
        echo_inv committed' sent' /\
        BT.buffer_wf model' /\
        BT.capacity model' == BT.capacity model /\
        step_post d model committed model' committed')
{
  BT.recall_model b;
  let view = BT.borrow_pending b;
  let len = BT.view_length view;
  let d = classify_pending (BT.view_data view) len;
  match d {
    Yield k l -> {
      lemma_yield_is_frame (BT.pending model);
      pts_to_len (BT.view_data view);
      pts_to_len out;
      let _sq = A.memcpy_l k (BT.view_data view) out;
      with ob1. assert (pts_to out ob1);
      assert (pure (Seq.equal (Seq.slice ob1 0 (SZ.v k))
                              (Seq.slice (BT.pending model) 0 (SZ.v k))));
      lemma_frame_of_yield model ob1 k l;
      BT.release_pending b view;
      let written = BT.write b out k;
      lemma_echo_inv_step committed sent (Seq.slice ob1 0 (SZ.v k));
      let _remaining = BT.commit_prefix b k;
      d
    }
    _ -> {
      BT.release_pending b view;
      d
    }
  }
}
#pop-options
