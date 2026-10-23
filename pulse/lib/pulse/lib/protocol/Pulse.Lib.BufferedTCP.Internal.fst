module Pulse.Lib.BufferedTCP.Internal

#lang-pulse

(**

  Protocol-independent, reusable specification *and imperative realisation* of a
  *buffered TCP receiver*.

  A buffered TCP endpoint splits the bytes it has received from the network into
  two contiguous regions:

    - a [committed] (a.k.a. delivered) prefix that has already been handed to the
      protocol and is no longer needed, and

    - a [pending] region — the received-but-not-yet-consumed bytes — which is
      physically held in a *fixed-capacity* array and always occupies the *dense
      prefix* (the first [pb_filled] slots) of that array.

  The full TCP received history is therefore, at every instant,

        tcp_received  ==  committed  ++  pending.

  This module gives the pure specs and the verified lemmas for the four
  transport-level obligations of that discipline:

    (1) [received_split]      full received = committed prefix ++ pending;
    (2) [pending]/[buffer_wf] pending is the dense prefix of the physical array,
                              of fixed capacity [capacity b];
    (3) [compact]/[committed_after] verified prefix commit + physical compaction
                              (consume a pending prefix, slide the tail down);
    (4) [append_read]         verified append of a freshly-read chunk, together
                              with the capacity ([chunk_fits]/[read_request_ok])
                              and no-zero-read ([can_read]) side conditions.

  It also provides the reusable *imperative* Pulse operation

    (5) [compact_buffer_suffix]  compact a physical [array U8.t] in place with
                              [Pulse.Lib.Memmove.memmove], with a postcondition tied
                              directly to the pure [compact] model above.  This is
                              exactly the compaction contract currently duplicated
                              in the TLS client and server drivers, so those local
                              copies can be deleted in favour of this one.

  The module reuses [Pulse.Lib.TCP.history] and the byte-prefix lemmas of
  [Pulse.Lib.Protocol.Implementation].  It is deliberately protocol independent: no
  state machine, wire format, or stream classifier appears here.  The
  scheduling / read-authorisation layer that consumes these specs lives in
  [Pulse.Lib.BufferedStream], which depends on this module (never the reverse).

  The imperative [read_append] helper below owns the complete masked-sub-array
  borrow/read/rejoin proof.  It is deliberately transport-only: scheduling
  authorization belongs to the endpoint abstraction in [Pulse.Lib.BufferedStream],
  whose exclusive read-ready state owns the concrete channel and backing array.
  This keeps the dependency direction:
  [Pulse.Lib.BufferedStream] depends on this transport layer, never the reverse.

**)

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module Seq = FStar.Seq
module SZ  = FStar.SizeT
module U8  = FStar.UInt8
module A   = Pulse.Lib.Array
module TCP = Pulse.Lib.TCP
module CPI = Pulse.Lib.Protocol.Implementation
module Memmove = Pulse.Lib.Memmove

(* ------------------------------------------------------------------ *)
(*  Pure sequence helpers                                             *)
(* ------------------------------------------------------------------ *)

(** The first [Seq.length a] bytes of [a ++ b] are exactly [a]. *)
let lemma_slice_append_l (#t:Type) (a b:Seq.seq t)
  : Lemma
      (ensures Seq.equal (Seq.slice (Seq.append a b) 0 (Seq.length a)) a)
= Seq.lemma_eq_intro (Seq.slice (Seq.append a b) 0 (Seq.length a)) a

(** The bytes of [a ++ b] past position [Seq.length a] are exactly [b]. *)
let lemma_slice_append_r (#t:Type) (a b:Seq.seq t)
  : Lemma
      (ensures
        Seq.equal
          (Seq.slice (Seq.append a b) (Seq.length a) (Seq.length a + Seq.length b))
          b)
= Seq.lemma_eq_intro
    (Seq.slice (Seq.append a b) (Seq.length a) (Seq.length a + Seq.length b))
    b

(** Re-glue two adjacent slices of the same sequence. *)
let lemma_recombine (#t:Type) (s:Seq.seq t) (n m:nat)
  : Lemma
      (requires n <= m /\ m <= Seq.length s)
      (ensures
        Seq.equal
          (Seq.append (Seq.slice s 0 n) (Seq.slice s n m))
          (Seq.slice s 0 m))
= Seq.lemma_split (Seq.slice s 0 m) n;
  Seq.lemma_eq_intro
    (Seq.append (Seq.slice s 0 n) (Seq.slice s n m))
    (Seq.slice s 0 m)

let lemma_take_drop (s:TCP.bytes) (n:nat)
  : Lemma
      (requires n <= Seq.length s)
      (ensures Seq.equal (Seq.append (take s n) (drop s n)) s)
= Seq.lemma_split s n;
  Seq.lemma_eq_intro (Seq.append (take s n) (drop s n)) s

(* ------------------------------------------------------------------ *)
(*  The physical fixed-capacity buffer                                *)
(* ------------------------------------------------------------------ *)

let lemma_live_wf (b:phys_buffer)
  : Lemma (requires buffer_wf b) (ensures live_count b == filled_count b)
= ()

(** Item (2): [pending] has length [pb_filled] and is a prefix of the array. *)
let lemma_pending_length (b:phys_buffer)
  : Lemma (requires buffer_wf b)
          (ensures Seq.length (pending b) == filled_count b)
= ()

let lemma_pending_dense_prefix (b:phys_buffer)
  : Lemma (requires buffer_wf b)
          (ensures TCP.bytes_exact_prefix (pending b) (buffer_data b))
= lemma_pending_length b

let lemma_free_space_wf (b:phys_buffer)
  : Lemma (requires buffer_wf b)
          (ensures free_space b == capacity b - filled_count b /\
                   filled_count b + free_space b == capacity b)
= ()

(* ------------------------------------------------------------------ *)
(*  Item (1): full received = committed prefix ++ pending             *)
(* ------------------------------------------------------------------ *)

(** The committed bytes are an exact byte-prefix of the received stream. *)
let lemma_committed_prefix (received committed:TCP.bytes) (b:phys_buffer)
  : Lemma (requires received_split received committed b)
          (ensures TCP.bytes_extends committed received)
= CPI.lemma_bytes_extends_append_equal committed received (pending b)

(** Dually, the pending region is the tail of the received stream. *)
let lemma_pending_is_tail (received committed:TCP.bytes) (b:phys_buffer)
  : Lemma (requires received_split received committed b)
          (ensures
            Seq.length committed <= Seq.length received /\
            Seq.equal (pending b)
              (Seq.slice received (Seq.length committed) (Seq.length received)))
= Seq.lemma_eq_elim received (Seq.append committed (pending b));
  lemma_slice_append_r committed (pending b)

(* ------------------------------------------------------------------ *)
(*  Item (3): prefix commit + physical compaction                     *)
(* ------------------------------------------------------------------ *)

(** Compaction preserves the fixed capacity and keeps the buffer well-formed. *)
let lemma_compact_capacity (b:phys_buffer) (n:nat)
  : Lemma (ensures capacity (compact b n) == capacity b)
= ()

let lemma_compact_wf (b:phys_buffer) (n:nat)
  : Lemma (ensures buffer_wf (compact b n))
= ()

let lemma_compact_filled (b:phys_buffer) (n:nat)
  : Lemma (requires buffer_wf b /\ n <= filled_count b)
          (ensures filled_count (compact b n) == filled_count b - n)
= ()

(** The pending region after compaction is the old pending with [n] bytes dropped. *)
let lemma_compact_pending (b:phys_buffer) (n:nat)
  : Lemma (requires buffer_wf b /\ n <= filled_count b)
          (ensures Seq.equal (pending (compact b n)) (drop (pending b) n))
= let f = filled_count b in
  lemma_slice_append_l
    (Seq.slice (buffer_data b) n f)
    (Seq.slice
      (buffer_data b)
      (f - n)
      (Seq.length (buffer_data b)));
  Seq.lemma_eq_intro (pending (compact b n)) (drop (pending b) n)

(** Committing extends the committed byte stream (reuses the CPI prefix lemma). *)
let lemma_committed_after_extends (committed:TCP.bytes) (b:phys_buffer) (n:nat)
  : Lemma (ensures TCP.bytes_extends committed (committed_after committed b n))
= CPI.lemma_bytes_extends_append committed (take (pending b) n)

(**
  Item (3), key law: a commit/compaction step preserves the full received
  stream — only the committed/pending boundary moves.
**)
let lemma_commit_preserves_full
  (received committed:TCP.bytes) (b:phys_buffer) (n:nat)
  : Lemma
      (requires
        received_split received committed b /\
        buffer_wf b /\
        n <= filled_count b)
      (ensures received_split received (committed_after committed b n) (compact b n))
= lemma_pending_length b;
  lemma_compact_pending b n;
  lemma_take_drop (pending b) n;
  // received == committed ++ pending b
  Seq.lemma_eq_elim received (Seq.append committed (pending b));
  // committed_after ++ pending(compact) == committed ++ (take ++ drop) == committed ++ pending b
  Seq.append_assoc committed (take (pending b) n) (pending (compact b n));
  Seq.lemma_eq_intro
    (Seq.append (committed_after committed b n) (pending (compact b n)))
    (Seq.append committed (pending b))

(* ------------------------------------------------------------------ *)
(*  Item (4): append-read, with capacity and no-zero-read conditions  *)
(* ------------------------------------------------------------------ *)

let lemma_append_read_capacity (b:phys_buffer) (chunk:TCP.bytes)
  : Lemma (ensures capacity (append_read b chunk) == capacity b)
= ()

let lemma_append_read_wf (b:phys_buffer) (chunk:TCP.bytes)
  : Lemma (requires buffer_wf b)
          (ensures buffer_wf (append_read b chunk))
= ()

let lemma_append_read_filled (b:phys_buffer) (chunk:TCP.bytes)
  : Lemma (requires buffer_wf b /\ chunk_fits b chunk)
          (ensures
            filled_count (append_read b chunk) ==
              filled_count b + Seq.length chunk)
= ()

(** The pending region grows by exactly the delivered chunk. *)
let lemma_append_read_pending (b:phys_buffer) (chunk:TCP.bytes)
  : Lemma (requires buffer_wf b /\ chunk_fits b chunk)
          (ensures Seq.equal (pending (append_read b chunk)) (Seq.append (pending b) chunk))
= let f = filled_count b in
  lemma_slice_append_l
    (Seq.slice (buffer_data b) 0 f)
    (Seq.append
      chunk
      (Seq.slice
        (buffer_data b)
        (f + Seq.length chunk)
        (Seq.length (buffer_data b))));
  lemma_slice_append_l
    chunk
    (Seq.slice
      (buffer_data b)
      (f + Seq.length chunk)
      (Seq.length (buffer_data b)));
  Seq.lemma_eq_intro (pending (append_read b chunk)) (Seq.append (pending b) chunk)

(** An append-read extends the pending region as a byte-prefix (old pending kept). *)
let lemma_append_read_pending_extends (b:phys_buffer) (chunk:TCP.bytes)
  : Lemma (requires buffer_wf b /\ chunk_fits b chunk)
          (ensures TCP.bytes_extends (pending b) (pending (append_read b chunk)))
= lemma_append_read_pending b chunk;
  CPI.lemma_bytes_extends_append_equal (pending b) (pending (append_read b chunk)) chunk

(**
  Item (4), key law: an append-read step extends the received stream by exactly
  the delivered chunk, keeping the [received = committed ++ pending] invariant.
**)
let lemma_append_read_extends_received
  (received committed:TCP.bytes) (b:phys_buffer) (chunk:TCP.bytes)
  : Lemma
      (requires received_split received committed b /\ buffer_wf b /\ chunk_fits b chunk)
      (ensures received_split (Seq.append received chunk) committed (append_read b chunk))
= lemma_append_read_pending b chunk;
  Seq.lemma_eq_elim received (Seq.append committed (pending b));
  Seq.append_assoc committed (pending b) chunk;
  Seq.lemma_eq_intro
    (Seq.append received chunk)
    (Seq.append committed (pending (append_read b chunk)))

(** The [Pulse.Lib.TCP.history] restatement of the append-read law. *)
let lemma_append_read_history
  (h:TCP.history) (committed:TCP.bytes) (b:phys_buffer) (chunk:TCP.bytes)
  : Lemma
      (requires history_received_split h committed b /\ buffer_wf b /\ chunk_fits b chunk)
      (ensures
        history_received_split (TCP.append_received h chunk) committed (append_read b chunk))
= lemma_append_read_extends_received h.TCP.tcp_received committed b chunk

(* ---- capacity / no-zero-read facts ---- *)

(** A read is possible exactly when the buffer is not full. *)
let lemma_can_read_iff (b:phys_buffer)
  : Lemma (requires buffer_wf b)
          (ensures (can_read b <==> filled_count b < capacity b))
= ()

(**
  Whenever the buffer is not full, requesting the whole free space is an
  admissible (non-zero, within-capacity) read request.
**)
let lemma_read_request_available (b:phys_buffer)
  : Lemma (requires buffer_wf b /\ can_read b)
          (ensures read_request_ok b (free_space b))
= ()

(**
  A full buffer admits *no* read request: the no-zero-read discipline forces a
  commit/compaction (to free space) before any further read.
**)
let lemma_full_no_read (b:phys_buffer) (max_len:nat)
  : Lemma (requires buffer_wf b /\ ~(can_read b))
          (ensures ~(read_request_ok b max_len))
= ()

(** Any chunk returned by an admissible read fits the buffer. *)
let lemma_read_chunk_fits (b:phys_buffer) (max_len:nat) (chunk:TCP.bytes)
  : Lemma (requires read_request_ok b max_len /\ Seq.length chunk <= max_len)
          (ensures chunk_fits b chunk)
= ()

(* ------------------------------------------------------------------ *)
(*  Initialisation                                                    *)
(* ------------------------------------------------------------------ *)

let lemma_empty_buffer_wf (cap:nat)
  : Lemma (ensures buffer_wf (empty_buffer cap) /\ capacity (empty_buffer cap) == cap)
= ()

let lemma_empty_buffer_pending (cap:nat)
  : Lemma (ensures Seq.equal (pending (empty_buffer cap)) Seq.empty)
= Seq.lemma_eq_intro (pending (empty_buffer cap)) Seq.empty

(** An empty buffer is consistent with an empty received/committed history. *)
let lemma_empty_buffer_received (cap:nat)
  : Lemma (ensures received_split Seq.empty Seq.empty (empty_buffer cap))
= lemma_empty_buffer_pending cap;
  Seq.append_empty_r (Seq.empty #U8.t);
  Seq.lemma_eq_intro
    (Seq.empty #U8.t)
    (Seq.append (Seq.empty #U8.t) (pending (empty_buffer cap)))

(* ------------------------------------------------------------------ *)
(*  Imperative realisation: in-place compaction over a physical array *)
(* ------------------------------------------------------------------ *)

(**
  The pure-model facts realised by an in-place front compaction of [consumed]
  bytes: the compacted buffer is well-formed, its live count is [buffered_len -
  consumed], and its pending region is exactly [data[consumed .. buffered_len)].
**)
let lemma_compact_suffix_model (data:TCP.bytes) (buffered_len consumed:nat)
  : Lemma
      (requires consumed <= buffered_len /\ buffered_len <= Seq.length data)
      (ensures (
        let b = mk_phys_buffer data buffered_len in
        buffer_wf b /\
        filled_count (compact b consumed) == buffered_len - consumed /\
        Seq.equal (pending (compact b consumed)) (Seq.slice data consumed buffered_len)))
= let b = mk_phys_buffer data buffered_len in
  lemma_pending_length b;
  lemma_compact_filled b consumed;
  lemma_compact_pending b consumed;
  Seq.lemma_eq_intro (pending (compact b consumed)) (Seq.slice data consumed buffered_len)

(**
  In-place compaction of the physical receive array: slide the still-pending
  suffix [raw[consumed_len .. buffered_len)] down to the front with
  [Pulse.Lib.Memmove.memmove], returning the new pending length.

  The postcondition is stated two ways: (a) the raw slice equality currently used
  verbatim by the TLS client and server drivers (so their local
  [compact_buffer_suffix] can be deleted and this called instead), and (b) the
  connection to the pure [compact] model — [Seq.slice raw_after 0 new_len] is
  exactly [pending (compact b consumed)] for the modelled buffer [b], and
  [new_len] is [filled_count (compact b consumed)] — so callers may reason with the
  pure model and [received_split] after calling it.
**)
fn compact_buffer_suffix
  (raw:array U8.t)
  (raw_capacity:SZ.t)
  (buffered_len:SZ.t)
  (consumed_len:SZ.t)
  requires pts_to raw 'raw_bytes **
           pure (Seq.length (Ghost.reveal 'raw_bytes) == SZ.v raw_capacity /\
                 SZ.v consumed_len <= SZ.v buffered_len /\
                 SZ.v buffered_len <= SZ.v raw_capacity)
  returns new_len:SZ.t
  ensures exists* raw_after.
           pts_to raw raw_after **
           pure (
             Seq.length raw_after == SZ.v raw_capacity /\
             Seq.length (Ghost.reveal 'raw_bytes) == SZ.v raw_capacity /\
             SZ.v consumed_len <= SZ.v buffered_len /\
             SZ.v buffered_len <= SZ.v raw_capacity /\
             new_len == pending_after_consumed buffered_len consumed_len /\
             SZ.v new_len + SZ.v consumed_len == SZ.v buffered_len /\
             SZ.v new_len <= SZ.v buffered_len /\
             // (a) raw slice equality — the drivers' verbatim contract
             Seq.equal
               (Seq.slice raw_after 0 (SZ.v new_len))
               (Seq.slice (Ghost.reveal 'raw_bytes)
                 (SZ.v consumed_len)
                 (SZ.v buffered_len)) /\
             // (b) pure-model connection to [compact] / [pending]
             buffer_wf (mk_phys_buffer (Ghost.reveal 'raw_bytes) (SZ.v buffered_len)) /\
             SZ.v new_len ==
               filled_count
                 (compact
                   (mk_phys_buffer (Ghost.reveal 'raw_bytes) (SZ.v buffered_len))
                   (SZ.v consumed_len)) /\
             Seq.equal
               (Seq.slice raw_after 0 (SZ.v new_len))
               (pending (compact (mk_phys_buffer (Ghost.reveal 'raw_bytes) (SZ.v buffered_len))
                                 (SZ.v consumed_len))))
{
  let new_len = SZ.sub buffered_len consumed_len;
  Memmove.memmove raw 0sz consumed_len new_len;
  lemma_compact_suffix_model (Ghost.reveal 'raw_bytes) (SZ.v buffered_len) (SZ.v consumed_len);
  new_len
}

(* ------------------------------------------------------------------ *)
(*  Imperative realisation: read into the free tail of the array      *)
(* ------------------------------------------------------------------ *)

(**
  The reusable transport read primitive.  Given the channel [ch], its backing
  fixed-capacity array [raw] with [filled] dense pending bytes at the front and a
  *strictly positive* free region ([filled < capacity]), borrow exactly the free
  tail [raw[filled .. capacity)], call [Pulse.Lib.TCP.read] on it (never touching the
  pending prefix), and rejoin.

  It preserves the array capacity and the old prefix
  [raw[0 .. filled)], and makes the new dense prefix exactly
  [old_pending ++ chunk] where [chunk] is the freshly received bytes; and it
  advances the channel history to [received ++ chunk].  The postcondition also
  connects to the pure model: the resulting buffer is well-formed, the chunk
  fits, and [pending after == pending before ++ chunk].

  No monotonic-history refs are touched — a caller advances those after this
  generic read.  The masked-sub-array borrow/read/rejoin (the proof duplicated in
  the TLS drivers) is entirely internal here.
**)
fn read_append
  (ch: TCP.channel)
  (raw: array U8.t)
  (capacity: SZ.t)
  (filled: SZ.t)
  (#received #sent: Ghost.erased TCP.bytes)
  requires TCP.is_channel ch received sent **
           pts_to raw 'raw_before **
           pure (Seq.length (Ghost.reveal 'raw_before) == SZ.v capacity /\
                 SZ.v filled < SZ.v capacity)
  returns res: read_append_result
  ensures exists* raw_after chunk.
           TCP.is_channel ch (Seq.append (Ghost.reveal received) chunk) (Ghost.reveal sent) **
           pts_to raw raw_after **
           pure (
             // capacity preserved, lengths, bounds
             Seq.length raw_after == SZ.v capacity /\
             Seq.length (Ghost.reveal 'raw_before) == SZ.v capacity /\
             SZ.v filled <= SZ.v capacity /\
             SZ.v (read_count res) <= SZ.v capacity - SZ.v filled /\
             SZ.v (total_count res) == SZ.v filled + SZ.v (read_count res) /\
             SZ.v (total_count res) <= SZ.v capacity /\
             Seq.length chunk == SZ.v (read_count res) /\
             // old pending prefix preserved
             Seq.equal (Seq.slice raw_after 0 (SZ.v filled))
                       (Seq.slice (Ghost.reveal 'raw_before) 0 (SZ.v filled)) /\
             // new dense prefix == old_pending ++ chunk
             Seq.equal (Seq.slice raw_after 0 (SZ.v (total_count res)))
                       (Seq.append (Seq.slice (Ghost.reveal 'raw_before) 0 (SZ.v filled)) chunk) /\
             // pure-model connection
             buffer_wf (mk_phys_buffer raw_after (SZ.v (total_count res))) /\
             chunk_fits (mk_phys_buffer (Ghost.reveal 'raw_before) (SZ.v filled)) chunk /\
             Seq.equal (pending (mk_phys_buffer raw_after (SZ.v (total_count res))))
                       (Seq.append (pending (mk_phys_buffer (Ghost.reveal 'raw_before) (SZ.v filled))) chunk))
{
  A.to_mask raw;
  with raw_mask. assert (A.pts_to_mask raw #1.0R raw_mask (fun _ -> True));
  assert (pure (Seq.length raw_mask == SZ.v capacity));
  assert (pure (forall (i:nat). i < Seq.length raw_mask ==>
    Seq.index raw_mask i == Some (Seq.index (Ghost.reveal 'raw_before) i)));
  let available = SZ.sub capacity filled;
  let tail = A.sub raw #1.0R #(fun _ -> True) filled (SZ.v capacity);
  with tail_mask. assert (A.pts_to_mask tail #1.0R tail_mask (fun _ -> True));
  assert (pure (Seq.length tail_mask == SZ.v available));
  assert (pure (forall (i:nat). i < Seq.length tail_mask ==> Some? (Seq.index tail_mask i)));
  A.from_mask tail;
  with tail_before. assert (pts_to tail tail_before);
  assert (pure (Seq.length tail_before == SZ.v available));
  let n = TCP.read ch tail available;
  with tail_after chunk. assert (
    TCP.is_channel ch (Seq.append (Ghost.reveal received) chunk) (Ghost.reveal sent) **
    pts_to tail tail_after);
  assert (pure (Seq.length tail_after == SZ.v available));
  assert (pure (Seq.length chunk == SZ.v n /\ SZ.v n <= SZ.v available));
  A.to_mask tail;
  with tail_mask_after. assert (A.pts_to_mask tail #1.0R tail_mask_after (fun _ -> True));
  rewrite (A.pts_to_mask tail #1.0R tail_mask_after (fun _ -> True))
       as (A.pts_to_mask (A.gsub raw (SZ.v filled) (SZ.v capacity)) #1.0R tail_mask_after (fun _ -> True));
  A.return_sub raw #1.0R #raw_mask #tail_mask_after
    #(fun k -> True /\ ~(SZ.v filled <= k /\ k < SZ.v capacity))
    #(fun _ -> True) #(SZ.v filled) #(SZ.v capacity);
  with joined_mask. assert (A.pts_to_mask raw #1.0R joined_mask
    (fun k -> (True /\ ~(SZ.v filled <= k /\ k < SZ.v capacity)) \/
              (SZ.v filled <= k /\ k < SZ.v capacity /\ True)));
  A.from_mask raw;
  with raw_after. assert (pts_to raw raw_after);
  assert (pure (Seq.length raw_after == SZ.v capacity));
  assert (pure (forall (i:nat). i < SZ.v capacity ==>
    Some (Seq.index raw_after i) == Seq.index joined_mask i));
  assert (pure (forall (i:nat). i < SZ.v capacity ==>
    Seq.index joined_mask i ==
      (if SZ.v filled <= i && i < SZ.v capacity
       then Seq.index tail_mask_after (i - SZ.v filled)
       else Seq.index raw_mask i)));
  assert (pure (forall (i:nat). i < SZ.v available ==>
    Seq.index tail_mask_after i == Some (Seq.index tail_after i)));
  assert (pure (Seq.equal chunk (Seq.slice tail_after 0 (SZ.v n))));
  assert (pure (forall (i:nat). i < SZ.v filled ==>
    Seq.index raw_after i == Seq.index (Ghost.reveal 'raw_before) i));
  assert (pure (forall (i:nat). i < SZ.v n ==>
    Seq.index raw_after (SZ.v filled + i) == Seq.index tail_after i));
  SZ.fits_lte (SZ.v filled + SZ.v n) (SZ.v capacity);
  let new_filled = SZ.add filled n;
  Seq.lemma_eq_intro (Seq.slice raw_after 0 (SZ.v filled))
                     (Seq.slice (Ghost.reveal 'raw_before) 0 (SZ.v filled));
  Seq.lemma_eq_intro (Seq.slice raw_after 0 (SZ.v new_filled))
                     (Seq.append (Seq.slice (Ghost.reveal 'raw_before) 0 (SZ.v filled)) chunk);
  Mkread_append_result n new_filled
}
