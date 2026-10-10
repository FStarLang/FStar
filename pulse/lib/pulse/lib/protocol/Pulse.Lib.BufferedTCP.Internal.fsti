module Pulse.Lib.BufferedTCP.Internal

#lang-pulse

(**
  Public contract for protocol-independent buffered TCP input.

  The pure model records a fixed-capacity backing sequence and the number of
  pending bytes densely stored at its front.  The imperative operations expose
  only verified in-place compaction and append-read; their masked-array proofs
  and sequence-manipulation helpers remain private to the implementation.
**)

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module Seq = FStar.Seq
module SZ  = FStar.SizeT
module U8  = FStar.UInt8
module TCP = Pulse.Lib.TCP

let take (s:TCP.bytes) (n:nat) : TCP.bytes =
  Seq.slice s 0 (if n <= Seq.length s then n else Seq.length s)

let drop (s:TCP.bytes) (n:nat) : TCP.bytes =
  Seq.slice s (if n <= Seq.length s then n else Seq.length s) (Seq.length s)

noeq
type phys_buffer = {
  pb_data   : TCP.bytes;
  pb_filled : nat;
}

let buffer_data (b:phys_buffer) : TCP.bytes =
  b.pb_data

let filled_count (b:phys_buffer) : nat =
  b.pb_filled

let buffer_wf (b:phys_buffer) : prop =
  filled_count b <= Seq.length (buffer_data b)

let capacity (b:phys_buffer) : nat =
  Seq.length (buffer_data b)

let live_count (b:phys_buffer) : nat =
  if filled_count b <= Seq.length (buffer_data b)
  then filled_count b
  else Seq.length (buffer_data b)

let pending (b:phys_buffer) : TCP.bytes =
  Seq.slice (buffer_data b) 0 (live_count b)

let free_space (b:phys_buffer) : nat =
  Seq.length (buffer_data b) - live_count b

val lemma_live_wf
  (b:phys_buffer)
  : Lemma
      (requires buffer_wf b)
      (ensures live_count b == filled_count b)

val lemma_pending_length
  (b:phys_buffer)
  : Lemma
      (requires buffer_wf b)
      (ensures Seq.length (pending b) == filled_count b)

val lemma_pending_dense_prefix
  (b:phys_buffer)
  : Lemma
      (requires buffer_wf b)
      (ensures TCP.bytes_exact_prefix (pending b) (buffer_data b))

val lemma_free_space_wf
  (b:phys_buffer)
  : Lemma
      (requires buffer_wf b)
      (ensures
        free_space b == capacity b - filled_count b /\
        filled_count b + free_space b == capacity b)

let received_split
  (received committed:TCP.bytes)
  (b:phys_buffer)
  : prop =
  Seq.equal received (Seq.append committed (pending b))

let history_received_split
  (h:TCP.history)
  (committed:TCP.bytes)
  (b:phys_buffer)
  : prop =
  received_split h.TCP.tcp_received committed b

val lemma_committed_prefix
  (received committed:TCP.bytes)
  (b:phys_buffer)
  : Lemma
      (requires received_split received committed b)
      (ensures TCP.bytes_extends committed received)

val lemma_pending_is_tail
  (received committed:TCP.bytes)
  (b:phys_buffer)
  : Lemma
      (requires received_split received committed b)
      (ensures
        Seq.length committed <= Seq.length received /\
        Seq.equal
          (pending b)
          (Seq.slice received (Seq.length committed) (Seq.length received)))

let committed_after
  (committed:TCP.bytes)
  (b:phys_buffer)
  (n:nat)
  : TCP.bytes =
  Seq.append committed (take (pending b) n)

let compact (b:phys_buffer) (n:nat) : phys_buffer =
  let f = live_count b in
  let k = if n <= f then n else f in
  {
    pb_data =
      Seq.append
        (Seq.slice (buffer_data b) k f)
        (Seq.slice
          (buffer_data b)
          (f - k)
          (Seq.length (buffer_data b)));
    pb_filled = f - k;
  }

val lemma_compact_capacity
  (b:phys_buffer)
  (n:nat)
  : Lemma
      (ensures capacity (compact b n) == capacity b)

val lemma_compact_wf
  (b:phys_buffer)
  (n:nat)
  : Lemma
      (ensures buffer_wf (compact b n))

val lemma_compact_filled
  (b:phys_buffer)
  (n:nat)
  : Lemma
      (requires buffer_wf b /\ n <= filled_count b)
      (ensures filled_count (compact b n) == filled_count b - n)

val lemma_compact_pending
  (b:phys_buffer)
  (n:nat)
  : Lemma
      (requires buffer_wf b /\ n <= filled_count b)
      (ensures Seq.equal (pending (compact b n)) (drop (pending b) n))

val lemma_committed_after_extends
  (committed:TCP.bytes)
  (b:phys_buffer)
  (n:nat)
  : Lemma
      (ensures TCP.bytes_extends committed (committed_after committed b n))

val lemma_commit_preserves_full
  (received committed:TCP.bytes)
  (b:phys_buffer)
  (n:nat)
  : Lemma
      (requires
        received_split received committed b /\
        buffer_wf b /\
        n <= filled_count b)
      (ensures
        received_split
          received
          (committed_after committed b n)
          (compact b n))

let chunk_fits (b:phys_buffer) (chunk:TCP.bytes) : prop =
  Seq.length chunk <= free_space b

let read_request_ok (b:phys_buffer) (max_len:nat) : prop =
  0 < max_len /\ max_len <= free_space b

let can_read (b:phys_buffer) : prop =
  free_space b > 0

let append_read (b:phys_buffer) (chunk:TCP.bytes) : phys_buffer =
  let f = live_count b in
  if f + Seq.length chunk <= Seq.length (buffer_data b)
  then
    {
      pb_data =
        Seq.append
          (Seq.slice (buffer_data b) 0 f)
          (Seq.append
            chunk
            (Seq.slice
              (buffer_data b)
              (f + Seq.length chunk)
              (Seq.length (buffer_data b))));
      pb_filled = f + Seq.length chunk;
    }
  else b

val lemma_append_read_capacity
  (b:phys_buffer)
  (chunk:TCP.bytes)
  : Lemma
      (ensures capacity (append_read b chunk) == capacity b)

val lemma_append_read_wf
  (b:phys_buffer)
  (chunk:TCP.bytes)
  : Lemma
      (requires buffer_wf b)
      (ensures buffer_wf (append_read b chunk))

val lemma_append_read_filled
  (b:phys_buffer)
  (chunk:TCP.bytes)
  : Lemma
      (requires buffer_wf b /\ chunk_fits b chunk)
      (ensures
        filled_count (append_read b chunk) ==
          filled_count b + Seq.length chunk)

val lemma_append_read_pending
  (b:phys_buffer)
  (chunk:TCP.bytes)
  : Lemma
      (requires buffer_wf b /\ chunk_fits b chunk)
      (ensures
        Seq.equal
          (pending (append_read b chunk))
          (Seq.append (pending b) chunk))

val lemma_append_read_pending_extends
  (b:phys_buffer)
  (chunk:TCP.bytes)
  : Lemma
      (requires buffer_wf b /\ chunk_fits b chunk)
      (ensures
        TCP.bytes_extends
          (pending b)
          (pending (append_read b chunk)))

val lemma_append_read_extends_received
  (received committed:TCP.bytes)
  (b:phys_buffer)
  (chunk:TCP.bytes)
  : Lemma
      (requires
        received_split received committed b /\
        buffer_wf b /\
        chunk_fits b chunk)
      (ensures
        received_split
          (Seq.append received chunk)
          committed
          (append_read b chunk))

val lemma_append_read_history
  (h:TCP.history)
  (committed:TCP.bytes)
  (b:phys_buffer)
  (chunk:TCP.bytes)
  : Lemma
      (requires
        history_received_split h committed b /\
        buffer_wf b /\
        chunk_fits b chunk)
      (ensures
        history_received_split
          (TCP.append_received h chunk)
          committed
          (append_read b chunk))

val lemma_can_read_iff
  (b:phys_buffer)
  : Lemma
      (requires buffer_wf b)
      (ensures (can_read b <==> filled_count b < capacity b))

val lemma_read_request_available
  (b:phys_buffer)
  : Lemma
      (requires buffer_wf b /\ can_read b)
      (ensures read_request_ok b (free_space b))

val lemma_full_no_read
  (b:phys_buffer)
  (max_len:nat)
  : Lemma
      (requires buffer_wf b /\ ~(can_read b))
      (ensures ~(read_request_ok b max_len))

val lemma_read_chunk_fits
  (b:phys_buffer)
  (max_len:nat)
  (chunk:TCP.bytes)
  : Lemma
      (requires
        read_request_ok b max_len /\
        Seq.length chunk <= max_len)
      (ensures chunk_fits b chunk)

let empty_buffer (cap:nat) : phys_buffer =
  { pb_data = Seq.create cap 0uy; pb_filled = 0 }

val lemma_empty_buffer_wf
  (cap:nat)
  : Lemma
      (ensures
        buffer_wf (empty_buffer cap) /\
        capacity (empty_buffer cap) == cap)

val lemma_empty_buffer_pending
  (cap:nat)
  : Lemma
      (ensures Seq.equal (pending (empty_buffer cap)) Seq.empty)

val lemma_empty_buffer_received
  (cap:nat)
  : Lemma
      (ensures received_split Seq.empty Seq.empty (empty_buffer cap))

let mk_phys_buffer (data:TCP.bytes) (filled:nat) : phys_buffer =
  { pb_data = data; pb_filled = filled }

let pending_after_consumed
  (buffered_len consumed_len:SZ.t)
  : SZ.t =
  if SZ.lte consumed_len buffered_len
  then SZ.sub buffered_len consumed_len
  else 0sz

fn compact_buffer_suffix
  (raw:array U8.t)
  (raw_capacity:SZ.t)
  (buffered_len:SZ.t)
  (consumed_len:SZ.t)
  requires
    pts_to raw 'raw_bytes **
    pure (
      Seq.length (Ghost.reveal 'raw_bytes) == SZ.v raw_capacity /\
      SZ.v consumed_len <= SZ.v buffered_len /\
      SZ.v buffered_len <= SZ.v raw_capacity)
  returns new_len:SZ.t
  ensures
    exists* raw_after.
      pts_to raw raw_after **
      pure (
        Seq.length raw_after == SZ.v raw_capacity /\
        Seq.length (Ghost.reveal 'raw_bytes) == SZ.v raw_capacity /\
        SZ.v consumed_len <= SZ.v buffered_len /\
        SZ.v buffered_len <= SZ.v raw_capacity /\
        new_len == pending_after_consumed buffered_len consumed_len /\
        SZ.v new_len + SZ.v consumed_len == SZ.v buffered_len /\
        SZ.v new_len <= SZ.v buffered_len /\
        Seq.equal
          (Seq.slice raw_after 0 (SZ.v new_len))
          (Seq.slice
            (Ghost.reveal 'raw_bytes)
            (SZ.v consumed_len)
            (SZ.v buffered_len)) /\
        buffer_wf
          (mk_phys_buffer
            (Ghost.reveal 'raw_bytes)
            (SZ.v buffered_len)) /\
        SZ.v new_len ==
          filled_count
            (compact
              (mk_phys_buffer
                (Ghost.reveal 'raw_bytes)
                (SZ.v buffered_len))
              (SZ.v consumed_len)) /\
        Seq.equal
          (Seq.slice raw_after 0 (SZ.v new_len))
          (pending
            (compact
              (mk_phys_buffer
                (Ghost.reveal 'raw_bytes)
                (SZ.v buffered_len))
              (SZ.v consumed_len))))

noeq
type read_append_result = {
  ra_read  : SZ.t;
  ra_total : SZ.t;
}

let read_count (res:read_append_result) : SZ.t =
  res.ra_read

let total_count (res:read_append_result) : SZ.t =
  res.ra_total

fn read_append
  (ch:TCP.channel)
  (raw:array U8.t)
  (capacity:SZ.t)
  (filled:SZ.t)
  (#received #sent:Ghost.erased TCP.bytes)
  requires
    TCP.is_channel ch received sent **
    pts_to raw 'raw_before **
    pure (
      Seq.length (Ghost.reveal 'raw_before) == SZ.v capacity /\
      SZ.v filled < SZ.v capacity)
  returns res:read_append_result
  ensures
    exists* raw_after chunk.
      TCP.is_channel
        ch
        (Seq.append (Ghost.reveal received) chunk)
        (Ghost.reveal sent) **
      pts_to raw raw_after **
      pure (
        Seq.length raw_after == SZ.v capacity /\
        Seq.length (Ghost.reveal 'raw_before) == SZ.v capacity /\
        SZ.v filled <= SZ.v capacity /\
        SZ.v (read_count res) <= SZ.v capacity - SZ.v filled /\
        SZ.v (total_count res) == SZ.v filled + SZ.v (read_count res) /\
        SZ.v (total_count res) <= SZ.v capacity /\
        Seq.length chunk == SZ.v (read_count res) /\
        Seq.equal
          (Seq.slice raw_after 0 (SZ.v filled))
          (Seq.slice
            (Ghost.reveal 'raw_before)
            0
            (SZ.v filled)) /\
        Seq.equal
          (Seq.slice raw_after 0 (SZ.v (total_count res)))
          (Seq.append
            (Seq.slice
              (Ghost.reveal 'raw_before)
              0
              (SZ.v filled))
            chunk) /\
        buffer_wf
          (mk_phys_buffer raw_after (SZ.v (total_count res))) /\
        chunk_fits
          (mk_phys_buffer
            (Ghost.reveal 'raw_before)
            (SZ.v filled))
          chunk /\
        Seq.equal
          (pending
            (mk_phys_buffer raw_after (SZ.v (total_count res))))
          (Seq.append
            (pending
              (mk_phys_buffer
                (Ghost.reveal 'raw_before)
                (SZ.v filled)))
            chunk))
