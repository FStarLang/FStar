module Pulse.Lib.BufferedTCP

#lang-pulse

(**
  Abstract ownership interface for a buffered TCP channel.

  A [t] exclusively owns a TCP channel, its fixed-capacity receive storage, and
  its current pending length.  Clients reason only about [phys_buffer], the
  logical model of that storage.  The concrete channel, array, length cell, and
  compaction machinery are hidden by [is_buffered].

  The scheduling layer in [Pulse.Lib.BufferedStream] is responsible for deciding
  when [read_more] may be called.  In particular, applications should receive a
  buffered-stream abstraction rather than the underlying [t].
**)

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module Seq = FStar.Seq
module SZ  = FStar.SizeT
module U8  = FStar.UInt8
module TCP = Pulse.Lib.TCP

type bytes = TCP.bytes

(* -------------------------------------------------------------------------- *)
(* Logical buffer model                                                       *)
(* -------------------------------------------------------------------------- *)

val phys_buffer : Type0

val pending : phys_buffer -> bytes
val capacity : phys_buffer -> nat

val buffer_wf : phys_buffer -> prop

let free_space (b:phys_buffer) : nat =
  if Seq.length (pending b) <= capacity b
  then capacity b - Seq.length (pending b)
  else 0

let can_read (b:phys_buffer) : prop =
  0 < free_space b

let chunk_fits (b:phys_buffer) (chunk:bytes) : prop =
  Seq.length chunk <= free_space b

let take (s:bytes) (n:nat) : bytes =
  Seq.slice s 0 (if n <= Seq.length s then n else Seq.length s)

let drop (s:bytes) (n:nat) : bytes =
  Seq.slice s (if n <= Seq.length s then n else Seq.length s) (Seq.length s)

let received_split
  (received delivered:bytes)
  (b:phys_buffer)
  : prop =
  Seq.equal received (Seq.append delivered (pending b))

let committed_after
  (delivered:bytes)
  (b:phys_buffer)
  (consumed:nat)
  : bytes =
  Seq.append delivered (take (pending b) consumed)

val compact : phys_buffer -> consumed:nat -> phys_buffer
val append_read : phys_buffer -> chunk:bytes -> phys_buffer

val lemma_pending_length
  (b:phys_buffer)
  : Lemma
      (requires buffer_wf b)
      (ensures Seq.length (pending b) <= capacity b)

val lemma_compact_wf
  (b:phys_buffer)
  (consumed:nat)
  : Lemma
      (requires buffer_wf b /\ consumed <= Seq.length (pending b))
      (ensures buffer_wf (compact b consumed))

val lemma_compact_pending
  (b:phys_buffer)
  (consumed:nat)
  : Lemma
      (requires buffer_wf b /\ consumed <= Seq.length (pending b))
      (ensures
        Seq.equal
          (pending (compact b consumed))
          (drop (pending b) consumed))

val lemma_committed_after_extends
  (delivered:bytes)
  (b:phys_buffer)
  (consumed:nat)
  : Lemma
      (ensures TCP.bytes_extends delivered (committed_after delivered b consumed))

val lemma_commit_preserves_full
  (received delivered:bytes)
  (b:phys_buffer)
  (consumed:nat)
  : Lemma
      (requires
        received_split received delivered b /\
        buffer_wf b /\
        consumed <= Seq.length (pending b))
      (ensures
        received_split
          received
          (committed_after delivered b consumed)
          (compact b consumed))

val lemma_append_read_wf
  (b:phys_buffer)
  (chunk:bytes)
  : Lemma
      (requires buffer_wf b /\ chunk_fits b chunk)
      (ensures buffer_wf (append_read b chunk))

val lemma_append_read_capacity
  (b:phys_buffer)
  (chunk:bytes)
  : Lemma
      (requires buffer_wf b /\ chunk_fits b chunk)
      (ensures capacity (append_read b chunk) == capacity b)

val lemma_append_read_pending
  (b:phys_buffer)
  (chunk:bytes)
  : Lemma
      (requires buffer_wf b /\ chunk_fits b chunk)
      (ensures
        Seq.equal
          (pending (append_read b chunk))
          (Seq.append (pending b) chunk))

val lemma_append_read_extends_received
  (received delivered:bytes)
  (b:phys_buffer)
  (chunk:bytes)
  : Lemma
      (requires
        received_split received delivered b /\
        buffer_wf b /\
        chunk_fits b chunk)
      (ensures
        received_split
          (Seq.append received chunk)
          delivered
          (append_read b chunk))

(* -------------------------------------------------------------------------- *)
(* Abstract buffered channel ownership                                        *)
(* -------------------------------------------------------------------------- *)

val t : Type0

val is_buffered :
  b:t ->
  model:phys_buffer ->
  received:bytes ->
  delivered:bytes ->
  sent:bytes ->
  slprop

val io_frame :
  b:t ->
  ch:TCP.channel ->
  model:phys_buffer ->
  received:bytes ->
  delivered:bytes ->
  sent:bytes ->
  slprop

ghost fn open_io_channel
  (b:t)
  (#model:erased phys_buffer)
  (#received #delivered #sent:erased bytes)
  requires
    is_buffered
      b
      (Ghost.reveal model)
      (Ghost.reveal received)
      (Ghost.reveal delivered)
      (Ghost.reveal sent)
  returns ch:TCP.channel
  ensures
    TCP.is_channel
      ch
      (Ghost.reveal received)
      (Ghost.reveal sent) **
    io_frame
      b
      ch
      (Ghost.reveal model)
      (Ghost.reveal received)
      (Ghost.reveal delivered)
      (Ghost.reveal sent)

ghost fn close_io_channel
  (b:t)
  (ch:TCP.channel)
  (#model:erased phys_buffer)
  (#received #delivered #sent:erased bytes)
  requires
    TCP.is_channel
      ch
      (Ghost.reveal received)
      (Ghost.reveal sent) **
    io_frame
      b
      ch
      (Ghost.reveal model)
      (Ghost.reveal received)
      (Ghost.reveal delivered)
      (Ghost.reveal sent)
  ensures
    is_buffered
      b
      (Ghost.reveal model)
      (Ghost.reveal received)
      (Ghost.reveal delivered)
      (Ghost.reveal sent)

ghost fn recall_model
  (b:t)
  (#model:erased phys_buffer)
  (#received #delivered #sent:erased bytes)
  requires
    is_buffered
      b
      (Ghost.reveal model)
      (Ghost.reveal received)
      (Ghost.reveal delivered)
      (Ghost.reveal sent)
  ensures
    is_buffered
      b
      (Ghost.reveal model)
      (Ghost.reveal received)
      (Ghost.reveal delivered)
      (Ghost.reveal sent) **
    pure (
      buffer_wf (Ghost.reveal model) /\
      received_split
        (Ghost.reveal received)
        (Ghost.reveal delivered)
        (Ghost.reveal model))

(* Reusable fixed-capacity storage while it is detached from a channel. *)
val storage : Type0

val same_storage :
  t ->
  storage ->
  prop

val lemma_same_storage_unique :
  b:t ->
  left:storage ->
  right:storage ->
  Lemma
    (requires same_storage b left /\ same_storage b right)
    (ensures left == right)

val is_storage :
  storage ->
  model:phys_buffer ->
  slprop

ghost fn recall_storage
  (storage:storage)
  (#model:erased phys_buffer)
  requires is_storage storage (Ghost.reveal model)
  ensures
    is_storage storage (Ghost.reveal model) **
    pure (
      buffer_wf (Ghost.reveal model) /\
      Seq.equal (pending (Ghost.reveal model)) Seq.empty)

fn alloc_storage
  (buffer_capacity:SZ.t)
  returns storage:storage
  ensures
    exists* model.
      is_storage storage model **
      pure (
       buffer_wf model /\
       capacity model == SZ.v buffer_capacity /\
       Seq.equal (pending model) Seq.empty)

fn attach
  (storage:storage)
  (ch:TCP.channel)
  (#model:erased phys_buffer)
  requires
    is_storage storage (Ghost.reveal model) **
    TCP.is_channel ch 'received 'sent **
    pure (
      buffer_wf (Ghost.reveal model) /\
      Seq.equal (pending (Ghost.reveal model)) Seq.empty)
  returns b:t
  ensures
    is_buffered
      b
      (Ghost.reveal model)
      (Ghost.reveal 'received)
      (Ghost.reveal 'received)
      (Ghost.reveal 'sent)
    **
    pure (same_storage b storage)

fn close_detach
  (b:t)
  (#model:erased phys_buffer)
  (#received #delivered #sent:erased bytes)
  requires
    is_buffered
      b
      (Ghost.reveal model)
      (Ghost.reveal received)
      (Ghost.reveal delivered)
      (Ghost.reveal sent)
  returns storage:storage
  ensures
    exists* model'.
      is_storage storage model' **
      pure (
       buffer_wf model' /\
       capacity model' == capacity (Ghost.reveal model) /\
       Seq.equal (pending model') Seq.empty /\
       same_storage b storage)

fn free_storage
  (storage:storage)
  (#model:erased phys_buffer)
  requires is_storage storage (Ghost.reveal model)
  ensures emp

fn wrap_empty
  (ch:TCP.channel)
  (buffer_capacity:SZ.t)
  requires TCP.is_channel ch 'received 'sent
  returns b:t
  ensures
    exists* model.
      is_buffered
        b
        model
        (Ghost.reveal 'received)
        (Ghost.reveal 'received)
        (Ghost.reveal 'sent) **
      pure (
        buffer_wf model /\
        capacity model == SZ.v buffer_capacity /\
        Seq.equal (pending model) Seq.empty)

fn pending_length
  (b:t)
  (#model:erased phys_buffer)
  (#received #delivered #sent:erased bytes)
  requires
    is_buffered
      b
      (Ghost.reveal model)
      (Ghost.reveal received)
      (Ghost.reveal delivered)
      (Ghost.reveal sent)
  returns len:SZ.t
  ensures
    is_buffered
      b
      (Ghost.reveal model)
      (Ghost.reveal received)
      (Ghost.reveal delivered)
      (Ghost.reveal sent) **
    pure (SZ.v len == Seq.length (pending (Ghost.reveal model)))

(* -------------------------------------------------------------------------- *)
(* Read-only pending view                                                     *)
(* -------------------------------------------------------------------------- *)

val pending_view : Type0
val view_data : pending_view -> array U8.t
val view_length : pending_view -> SZ.t

val buffered_frame :
  b:t ->
  view:pending_view ->
  model:phys_buffer ->
  received:bytes ->
  delivered:bytes ->
  sent:bytes ->
  slprop

fn borrow_pending
  (b:t)
  (#model:erased phys_buffer)
  (#received #delivered #sent:erased bytes)
  requires
    is_buffered
      b
      (Ghost.reveal model)
      (Ghost.reveal received)
      (Ghost.reveal delivered)
      (Ghost.reveal sent)
  returns view:pending_view
  ensures
    pts_to (view_data view) (pending (Ghost.reveal model)) **
    buffered_frame
      b
      view
      (Ghost.reveal model)
      (Ghost.reveal received)
      (Ghost.reveal delivered)
      (Ghost.reveal sent) **
    pure (SZ.v (view_length view) == Seq.length (pending (Ghost.reveal model)))

fn release_pending
  (b:t)
  (view:pending_view)
  (#model:erased phys_buffer)
  (#received #delivered #sent:erased bytes)
  requires
    pts_to (view_data view) (pending (Ghost.reveal model)) **
    buffered_frame
      b
      view
      (Ghost.reveal model)
      (Ghost.reveal received)
      (Ghost.reveal delivered)
      (Ghost.reveal sent)
  ensures
    is_buffered
      b
      (Ghost.reveal model)
      (Ghost.reveal received)
      (Ghost.reveal delivered)
      (Ghost.reveal sent)

(* -------------------------------------------------------------------------- *)
(* State transitions                                                          *)
(* -------------------------------------------------------------------------- *)

fn commit_prefix
  (b:t)
  (consumed:SZ.t)
  (#model:erased phys_buffer)
  (#received #delivered #sent:erased bytes)
  requires
    is_buffered
      b
      (Ghost.reveal model)
      (Ghost.reveal received)
      (Ghost.reveal delivered)
      (Ghost.reveal sent) **
    pure (SZ.v consumed <= Seq.length (pending (Ghost.reveal model)))
  returns remaining:SZ.t
  ensures
    exists* model'.
      is_buffered
        b
        model'
        (Ghost.reveal received)
        (committed_after
          (Ghost.reveal delivered)
          (Ghost.reveal model)
          (SZ.v consumed))
        (Ghost.reveal sent) **
      pure (
        model' == compact (Ghost.reveal model) (SZ.v consumed) /\
        buffer_wf model' /\
        capacity model' == capacity (Ghost.reveal model) /\
        Seq.equal
          (pending model')
          (drop (pending (Ghost.reveal model)) (SZ.v consumed)) /\
        SZ.v remaining == Seq.length (pending model'))

fn read_more
  (b:t)
  (#model:erased phys_buffer)
  (#received #delivered #sent:erased bytes)
  requires
    is_buffered
      b
      (Ghost.reveal model)
      (Ghost.reveal received)
      (Ghost.reveal delivered)
      (Ghost.reveal sent) **
    pure (buffer_wf (Ghost.reveal model) /\ can_read (Ghost.reveal model))
  returns read_len:SZ.t
  ensures
    exists* chunk model'.
      is_buffered
        b
        model'
        (Seq.append (Ghost.reveal received) chunk)
        (Ghost.reveal delivered)
        (Ghost.reveal sent) **
      pure (
        Seq.length chunk == SZ.v read_len /\
        chunk_fits (Ghost.reveal model) chunk /\
        buffer_wf model' /\
        capacity model' == capacity (Ghost.reveal model) /\
        Seq.equal
          (pending model')
          (Seq.append (pending (Ghost.reveal model)) chunk))

fn write
  (b:t)
  (data:array U8.t)
  (len:SZ.t)
  (#model:erased phys_buffer)
  (#received #delivered #sent:erased bytes)
  requires
    is_buffered
      b
      (Ghost.reveal model)
      (Ghost.reveal received)
      (Ghost.reveal delivered)
      (Ghost.reveal sent) **
    pts_to data 'bytes **
    pure (SZ.v len <= Seq.length (Ghost.reveal 'bytes))
  returns written:SZ.t
  ensures
    is_buffered
      b
      (Ghost.reveal model)
      (Ghost.reveal received)
      (Ghost.reveal delivered)
      (Seq.append
        (Ghost.reveal sent)
        (if SZ.v written <= Seq.length (Ghost.reveal 'bytes)
         then Seq.slice (Ghost.reveal 'bytes) 0 (SZ.v written)
         else Seq.create 0 0uy)) **
    pts_to data 'bytes **
    pure (written == len)

fn close
  (b:t)
  (#model:erased phys_buffer)
  (#received #delivered #sent:erased bytes)
  requires
    is_buffered
      b
      (Ghost.reveal model)
      (Ghost.reveal received)
      (Ghost.reveal delivered)
      (Ghost.reveal sent)
  ensures emp
