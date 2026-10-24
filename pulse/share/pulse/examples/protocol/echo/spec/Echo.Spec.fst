module Echo.Spec

(**
  Pure specification of a length-prefixed echo protocol.

  A frame is a 2-byte big-endian payload length [L], with
  [1 <= L <= max_payload], followed by [L] payload bytes.  The server reads
  frames and writes each one back unchanged (header included).

  This module gives:
    * [classify], a pure frame classifier (need-more / complete / malformed),
      packaged as a [Pulse.Lib.BufferedStream.Classifier.stream_processor]
      instance [echo_sp] whose two laws (bounded consumption and prefix
      stability) are proved here;
    * [is_frames], the predicate "this byte string is a concatenation of
      well-formed frames";
    * [echo_inv committed sent], the server's correctness invariant: the bytes
      sent equal the bytes consumed so far, and those are a sequence of
      well-formed frames.
**)

module Seq = FStar.Seq
module SZ  = FStar.SizeT
module U8  = FStar.UInt8
module TCP = Pulse.Lib.TCP

open Pulse.Lib.BufferedStream.Classifier

unfold type bytes = TCP.bytes

let header_len : nat = 2
let max_payload : nat = 256
let max_frame : nat = header_len + max_payload

type echo_error =
  | Malformed
  | PeerClosed

(* ------------------------------------------------------------------ *)
(* The pure classifier                                                *)
(* ------------------------------------------------------------------ *)

noextract
let payload_len (s:bytes{Seq.length s >= 2}) : nat =
  U8.v (Seq.index s 0) * 256 + U8.v (Seq.index s 1)

(** [Yield consumed payload]: a complete frame of [consumed] bytes, of which
    [payload] are payload. *)
noextract
let classify (_:unit) (s:bytes) : classification SZ.t echo_error =
  if Seq.length s < header_len then NeedMore
  else
    let l = payload_len s in
    if l = 0 || l > max_payload then Reject Malformed
    else if Seq.length s < header_len + l then NeedMore
    else Yield (SZ.uint_to_t (header_len + l)) (SZ.uint_to_t l)

noextract
let lemma_classify_consumption (st:unit) (p:bytes)
  : Lemma (consumption_law classify st p)
= ()

noextract
let lemma_classify_prefix_stable (st:unit) (p extra:bytes)
  : Lemma
      (requires is_conclusive (classify st p))
      (ensures classify st (Seq.append p extra) == classify st p)
= Seq.lemma_index_app1 p extra 0;
  Seq.lemma_index_app1 p extra 1

noextract
instance echo_sp : stream_processor unit SZ.t echo_error = {
  sp_classify = classify;
  sp_consumption = lemma_classify_consumption;
  sp_prefix_stable = lemma_classify_prefix_stable;
}

(** A NeedMore decision is only ever made on fewer than [max_frame] bytes, so
    a receive buffer of capacity [>= max_frame] always has room to read. *)
let lemma_needmore_short (p:bytes)
  : Lemma
      (requires needs_more echo_sp () p)
      (ensures Seq.length p < max_frame)
= ()

(* ------------------------------------------------------------------ *)
(* Frame sequences                                                    *)
(* ------------------------------------------------------------------ *)

noextract
let is_frame (f:bytes) : prop =
  Seq.length f >= header_len /\
  (let l = payload_len f in
   1 <= l /\ l <= max_payload /\ Seq.length f == header_len + l)

noextract
let rec is_frames (s:bytes) : Tot bool (decreases Seq.length s) =
  if Seq.length s = 0 then true
  else if Seq.length s < header_len then false
  else
    let l = payload_len s in
    if l = 0 || l > max_payload || Seq.length s < header_len + l then false
    else is_frames (Seq.slice s (header_len + l) (Seq.length s))

(** A [Yield k _] decision delimits exactly one well-formed frame. *)
let lemma_yield_is_frame (p:bytes)
  : Lemma
      (requires Yield? (classify () p))
      (ensures
        (let k = SZ.v (Yield?.consumed (classify () p)) in
         k <= Seq.length p /\
         is_frame (Seq.slice p 0 k)))
= ()

let rec lemma_is_frames_snoc (d f:bytes)
  : Lemma
      (requires is_frames d /\ is_frame f)
      (ensures is_frames (Seq.append d f))
      (decreases Seq.length d)
= if Seq.length d = 0
  then begin
    Seq.lemma_eq_elim (Seq.append d f) f;
    let l = payload_len f in
    assert (Seq.length (Seq.slice f (header_len + l) (Seq.length f)) = 0)
  end
  else begin
    let l = payload_len d in
    Seq.lemma_index_app1 d f 0;
    Seq.lemma_index_app1 d f 1;
    let rest = Seq.slice d (header_len + l) (Seq.length d) in
    lemma_is_frames_snoc rest f;
    let df = Seq.append d f in
    Seq.lemma_eq_elim
      (Seq.slice df (header_len + l) (Seq.length df))
      (Seq.append rest f)
  end

(* ------------------------------------------------------------------ *)
(* The echo server invariant                                          *)
(* ------------------------------------------------------------------ *)

(** Everything the server has consumed is a sequence of well-formed frames,
    and it has sent back exactly those bytes. *)
noextract
let echo_inv (committed sent:bytes) : prop =
  sent == committed /\ is_frames committed

let lemma_echo_inv_empty (r s:bytes)
  : Lemma
      (requires Seq.length r == 0 /\ Seq.length s == 0)
      (ensures echo_inv r s)
= Seq.lemma_eq_elim r s

(** Echoing one more frame (consumed as a [Yield] prefix [f] of the pending
    bytes) preserves the invariant. *)
let lemma_echo_inv_step (committed sent f:bytes)
  : Lemma
      (requires echo_inv committed sent /\ is_frame f)
      (ensures echo_inv (Seq.append committed f) (Seq.append sent f))
= lemma_is_frames_snoc committed f
