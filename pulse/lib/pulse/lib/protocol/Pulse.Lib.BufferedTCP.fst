module Pulse.Lib.BufferedTCP

#lang-pulse

open Pulse.Lib.Pervasives
open Pulse.Lib.Array.PtsTo

module Seq  = FStar.Seq
module SeqP = FStar.Seq.Properties
module SZ   = FStar.SizeT
module U8   = FStar.UInt8
module A    = Pulse.Lib.Array
module Box  = Pulse.Lib.Box
module V    = Pulse.Lib.Vec
module TCP  = Pulse.Lib.TCP
module I    = Pulse.Lib.BufferedTCP.Internal

type phys_buffer = I.phys_buffer

let pending = I.pending
let capacity = I.capacity
let buffer_wf = I.buffer_wf
let compact = I.compact
let append_read = I.append_read

let lemma_pending_length (b:phys_buffer)
  : Lemma
      (requires buffer_wf b)
      (ensures Seq.length (pending b) <= capacity b)
= I.lemma_pending_length b;
  I.lemma_live_wf b

let lemma_compact_wf (b:phys_buffer) (consumed:nat)
  : Lemma
      (requires buffer_wf b /\ consumed <= Seq.length (pending b))
      (ensures buffer_wf (compact b consumed))
= I.lemma_pending_length b;
  I.lemma_compact_wf b consumed

let lemma_compact_pending (b:phys_buffer) (consumed:nat)
  : Lemma
      (requires buffer_wf b /\ consumed <= Seq.length (pending b))
      (ensures
        Seq.equal
          (pending (compact b consumed))
          (drop (pending b) consumed))
= I.lemma_pending_length b;
  I.lemma_compact_pending b consumed

let lemma_committed_after_extends
  (delivered:bytes)
  (b:phys_buffer)
  (consumed:nat)
  : Lemma
      (ensures TCP.bytes_extends delivered (committed_after delivered b consumed))
= I.lemma_committed_after_extends delivered b consumed

let lemma_commit_preserves_full
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
= I.lemma_pending_length b;
  I.lemma_commit_preserves_full received delivered b consumed

let lemma_append_read_wf (b:phys_buffer) (chunk:bytes)
  : Lemma
      (requires buffer_wf b /\ chunk_fits b chunk)
      (ensures buffer_wf (append_read b chunk))
= I.lemma_live_wf b;
  I.lemma_append_read_wf b chunk

let lemma_append_read_capacity (b:phys_buffer) (chunk:bytes)
  : Lemma
      (requires buffer_wf b /\ chunk_fits b chunk)
      (ensures capacity (append_read b chunk) == capacity b)
= I.lemma_append_read_capacity b chunk

let lemma_append_read_pending (b:phys_buffer) (chunk:bytes)
  : Lemma
      (requires buffer_wf b /\ chunk_fits b chunk)
      (ensures
        Seq.equal
          (pending (append_read b chunk))
          (Seq.append (pending b) chunk))
= I.lemma_live_wf b;
  I.lemma_append_read_pending b chunk

let lemma_append_read_extends_received
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
= I.lemma_live_wf b;
  I.lemma_append_read_extends_received received delivered b chunk

noeq
type t = {
  bt_channel: TCP.channel;
  bt_storage: V.vec U8.t;
  bt_filled: Box.box SZ.t;
  bt_capacity: SZ.t;
}

let is_buffered
  (b:t)
  (model:phys_buffer)
  (received delivered sent:bytes)
  : slprop =
  exists* raw filled.
    TCP.is_channel b.bt_channel received sent **
    V.pts_to b.bt_storage #1.0R raw **
    Box.pts_to b.bt_filled filled **
    pure (
      V.is_full_vec b.bt_storage /\
      Seq.length raw == SZ.v b.bt_capacity /\
      SZ.v filled <= SZ.v b.bt_capacity /\
      buffer_wf model /\
      capacity model == SZ.v b.bt_capacity /\
      Seq.equal (pending model) (Seq.slice raw 0 (SZ.v filled)) /\
      received_split received delivered model)

let io_frame
  (b:t)
  (ch:TCP.channel)
  (model:phys_buffer)
  (received delivered sent:bytes)
  : slprop =
  exists* raw filled.
    V.pts_to b.bt_storage #1.0R raw **
    Box.pts_to b.bt_filled filled **
    pure (
      ch == b.bt_channel /\
      V.is_full_vec b.bt_storage /\
      Seq.length raw == SZ.v b.bt_capacity /\
      SZ.v filled <= SZ.v b.bt_capacity /\
      buffer_wf model /\
      capacity model == SZ.v b.bt_capacity /\
      Seq.equal (pending model) (Seq.slice raw 0 (SZ.v filled)) /\
      received_split received delivered model)

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
{
  unfold (is_buffered
    b
    (Ghost.reveal model)
    (Ghost.reveal received)
    (Ghost.reveal delivered)
    (Ghost.reveal sent));
  with raw filled. _;
  fold (io_frame
    b
    b.bt_channel
    (Ghost.reveal model)
    (Ghost.reveal received)
    (Ghost.reveal delivered)
    (Ghost.reveal sent));
  b.bt_channel
}

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
{
  unfold (io_frame
    b
    ch
    (Ghost.reveal model)
    (Ghost.reveal received)
    (Ghost.reveal delivered)
    (Ghost.reveal sent));
  with raw filled. _;
  assert (pure (ch == b.bt_channel));
  rewrite (TCP.is_channel
    ch
    (Ghost.reveal received)
    (Ghost.reveal sent))
    as (TCP.is_channel
      b.bt_channel
      (Ghost.reveal received)
      (Ghost.reveal sent));
  fold (is_buffered
    b
    (Ghost.reveal model)
    (Ghost.reveal received)
    (Ghost.reveal delivered)
    (Ghost.reveal sent))
}

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
{
  unfold (is_buffered
    b
    (Ghost.reveal model)
    (Ghost.reveal received)
    (Ghost.reveal delivered)
    (Ghost.reveal sent));
  fold (is_buffered
    b
    (Ghost.reveal model)
    (Ghost.reveal received)
    (Ghost.reveal delivered)
    (Ghost.reveal sent))
}

noeq
type storage = {
  bs_storage: V.vec U8.t;
  bs_filled: Box.box SZ.t;
  bs_capacity: SZ.t;
}

let same_storage
  (b:t)
  (storage:storage)
  : prop =
  b.bt_storage == storage.bs_storage /\
  b.bt_filled == storage.bs_filled /\
  b.bt_capacity == storage.bs_capacity

let lemma_same_storage_unique
  (b:t)
  (left right:storage)
  : Lemma
      (requires same_storage b left /\ same_storage b right)
      (ensures left == right)
=
  assert (left.bs_storage == right.bs_storage);
  assert (left.bs_filled == right.bs_filled);
  assert (left.bs_capacity == right.bs_capacity)

let is_storage
  (storage:storage)
  (model:phys_buffer)
  : slprop =
  exists* raw.
    V.pts_to storage.bs_storage #1.0R raw **
    Box.pts_to storage.bs_filled 0sz **
    pure (
      V.is_full_vec storage.bs_storage /\
      Seq.length raw == SZ.v storage.bs_capacity /\
      buffer_wf model /\
      capacity model == SZ.v storage.bs_capacity /\
      Seq.equal (pending model) Seq.empty)

ghost fn recall_storage
  (storage:storage)
  (#model:erased phys_buffer)
  requires is_storage storage (Ghost.reveal model)
  ensures
    is_storage storage (Ghost.reveal model) **
    pure (
      buffer_wf (Ghost.reveal model) /\
      Seq.equal (pending (Ghost.reveal model)) Seq.empty)
{
  unfold (is_storage storage (Ghost.reveal model));
  fold (is_storage storage (Ghost.reveal model))
}

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
{
  let raw = V.alloc 0uy buffer_capacity;
  let filled = Box.alloc 0sz;
  let storage = {
    bs_storage = raw;
    bs_filled = filled;
    bs_capacity = buffer_capacity;
  };
  let model : erased phys_buffer =
    Ghost.hide (I.empty_buffer (SZ.v buffer_capacity));
  I.lemma_empty_buffer_wf (SZ.v buffer_capacity);
  I.lemma_empty_buffer_pending (SZ.v buffer_capacity);
  rewrite
    (V.pts_to raw #1.0R (Seq.create (SZ.v buffer_capacity) 0uy))
    as
    (V.pts_to
      storage.bs_storage
      #1.0R
      (Seq.create (SZ.v storage.bs_capacity) 0uy));
  rewrite
    (Box.pts_to filled 0sz)
    as
    (Box.pts_to storage.bs_filled 0sz);
  fold (is_storage storage (Ghost.reveal model));
  storage
}

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
{
  unfold (is_storage storage (Ghost.reveal model));
  with raw.
    assert (
      V.pts_to storage.bs_storage #1.0R raw **
      Box.pts_to storage.bs_filled 0sz);
  let b = {
    bt_channel = ch;
    bt_storage = storage.bs_storage;
    bt_filled = storage.bs_filled;
    bt_capacity = storage.bs_capacity;
  };
  Seq.append_empty_r (Ghost.reveal 'received);
  assert (pure (received_split
    (Ghost.reveal 'received)
    (Ghost.reveal 'received)
    (Ghost.reveal model)));
  rewrite
    (TCP.is_channel ch 'received 'sent)
    as
    (TCP.is_channel b.bt_channel 'received 'sent);
  rewrite
    (V.pts_to storage.bs_storage #1.0R raw)
    as
    (V.pts_to b.bt_storage #1.0R raw);
  rewrite
    (Box.pts_to storage.bs_filled 0sz)
    as
    (Box.pts_to b.bt_filled 0sz);
  fold (is_buffered
    b
    (Ghost.reveal model)
    (Ghost.reveal 'received)
    (Ghost.reveal 'received)
    (Ghost.reveal 'sent));
  b
}

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
{
  unfold (is_buffered
    b
    (Ghost.reveal model)
    (Ghost.reveal received)
    (Ghost.reveal delivered)
    (Ghost.reveal sent));
  with raw filled.
    assert (
      TCP.is_channel
        b.bt_channel
        (Ghost.reveal received)
        (Ghost.reveal sent) **
      V.pts_to b.bt_storage #1.0R raw **
      Box.pts_to b.bt_filled filled);
  TCP.close b.bt_channel;
  Box.(b.bt_filled := 0sz);
  let storage = {
    bs_storage = b.bt_storage;
    bs_filled = b.bt_filled;
    bs_capacity = b.bt_capacity;
  };
  let model' : erased phys_buffer =
    Ghost.hide (I.mk_phys_buffer raw 0);
  assert (pure (buffer_wf (Ghost.reveal model')));
  assert (pure (
    capacity (Ghost.reveal model') == capacity (Ghost.reveal model)));
  Seq.lemma_eq_intro (pending (Ghost.reveal model')) Seq.empty;
  rewrite
    (V.pts_to b.bt_storage #1.0R raw)
    as
    (V.pts_to storage.bs_storage #1.0R raw);
  rewrite
    (Box.pts_to b.bt_filled 0sz)
    as
    (Box.pts_to storage.bs_filled 0sz);
  fold (is_storage storage (Ghost.reveal model'));
  storage
}

fn free_storage
  (storage:storage)
  (#model:erased phys_buffer)
  requires is_storage storage (Ghost.reveal model)
  ensures emp
{
  unfold (is_storage storage (Ghost.reveal model));
  V.free storage.bs_storage;
  Box.free storage.bs_filled
}

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
{
  let storage = alloc_storage buffer_capacity;
  with model.
    assert (
      is_storage storage model **
      pure (
        buffer_wf model /\
        capacity model == SZ.v buffer_capacity /\
        Seq.equal (pending model) Seq.empty));
  attach storage ch
}

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
{
  unfold (is_buffered
    b
    (Ghost.reveal model)
    (Ghost.reveal received)
    (Ghost.reveal delivered)
    (Ghost.reveal sent));
  with raw filled.
    assert (
      V.pts_to b.bt_storage #1.0R raw **
      Box.pts_to b.bt_filled filled);
  let len = Box.(!b.bt_filled);
  assert (pure (len == filled));
  Seq.lemma_len_slice raw 0 (SZ.v filled);
  assert (pure (SZ.v len == Seq.length (pending (Ghost.reveal model))));
  fold (is_buffered
    b
    (Ghost.reveal model)
    (Ghost.reveal received)
    (Ghost.reveal delivered)
    (Ghost.reveal sent));
  len
}

noeq
type pending_view = {
  pv_parent: array U8.t;
  pv_length: len:SZ.t { SZ.v len <= A.length pv_parent };
  pv_data:
    data:array U8.t {
      data == A.gsub pv_parent 0 (SZ.v pv_length)
    };
  pv_raw_before: Ghost.erased bytes;
}

let view_data (view:pending_view) : array U8.t =
  view.pv_data

let view_length (view:pending_view) : SZ.t =
  view.pv_length

let buffered_frame
  (b:t)
  (view:pending_view)
  (model:phys_buffer)
  (received delivered sent:bytes)
  : slprop =
  exists* raw_mask.
    TCP.is_channel b.bt_channel received sent **
    Box.pts_to b.bt_filled view.pv_length **
    A.pts_to_mask
      (V.vec_to_array b.bt_storage)
      #1.0R
      raw_mask
      (fun i -> True /\ ~(0 <= i /\ i < SZ.v view.pv_length)) **
    pure (
      view.pv_parent == V.vec_to_array b.bt_storage /\
      V.is_full_vec b.bt_storage /\
      Seq.length (Ghost.reveal view.pv_raw_before) == SZ.v b.bt_capacity /\
      SZ.v view.pv_length <= SZ.v b.bt_capacity /\
      Seq.length raw_mask ==
        Seq.length (Ghost.reveal view.pv_raw_before) /\
      (forall (i:nat). i < Seq.length raw_mask ==>
        Seq.index raw_mask i ==
          Some (Seq.index (Ghost.reveal view.pv_raw_before) i)) /\
      buffer_wf model /\
      capacity model == SZ.v b.bt_capacity /\
      Seq.equal
        (pending model)
        (Seq.slice
          (Ghost.reveal view.pv_raw_before)
          0
          (SZ.v view.pv_length)) /\
      received_split received delivered model)

let lemma_rejoined_mask
  (raw_before prefix:bytes)
  (raw_mask prefix_mask joined_mask:Seq.seq (option U8.t))
  (prefix_len:nat)
  : Lemma
      (requires
        Seq.length raw_mask == Seq.length raw_before /\
        Seq.length joined_mask == Seq.length raw_mask /\
        Seq.length prefix_mask == prefix_len /\
        prefix_len <= Seq.length raw_before /\
        Seq.equal prefix (Seq.slice raw_before 0 prefix_len) /\
        (forall (i:nat). i < Seq.length raw_mask ==>
          Seq.index raw_mask i == Some (Seq.index raw_before i)) /\
        (forall (i:nat). i < Seq.length prefix_mask ==>
          Seq.index prefix_mask i == Some (Seq.index prefix i)) /\
        (forall (i:nat). i < Seq.length joined_mask ==>
          Seq.index joined_mask i ==
            (if i < prefix_len
             then Seq.index prefix_mask i
             else Seq.index raw_mask i)))
      (ensures
        forall (i:nat). i < Seq.length joined_mask ==>
          Seq.index joined_mask i == Some (Seq.index raw_before i))
=
  let index_proof
    (i:nat { i < Seq.length joined_mask })
    : Lemma
        (Seq.index joined_mask i == Some (Seq.index raw_before i))
  =
    if i < prefix_len then (
      Seq.lemma_eq_elim prefix (Seq.slice raw_before 0 prefix_len);
      Seq.lemma_index_slice raw_before 0 prefix_len i
    ) else (
      assert (i < Seq.length raw_mask)
    )
  in
  FStar.Classical.forall_intro
    #(i:nat { i < Seq.length joined_mask })
    #(fun i ->
      Seq.index joined_mask i == Some (Seq.index raw_before i))
    index_proof

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
{
  unfold (is_buffered
    b
    (Ghost.reveal model)
    (Ghost.reveal received)
    (Ghost.reveal delivered)
    (Ghost.reveal sent));
  with raw filled.
    assert (
      TCP.is_channel
        b.bt_channel
        (Ghost.reveal received)
        (Ghost.reveal sent) **
      V.pts_to b.bt_storage #1.0R raw **
      Box.pts_to b.bt_filled filled);
  let current = Box.(!b.bt_filled);
  assert (pure (current == filled));
  rewrite
    (Box.pts_to b.bt_filled filled)
    as
    (Box.pts_to b.bt_filled current);
  V.to_array_pts_to b.bt_storage;
  A.to_mask (V.vec_to_array b.bt_storage);
  with raw_mask.
    assert (A.pts_to_mask
      (V.vec_to_array b.bt_storage)
      #1.0R
      raw_mask
      (fun _ -> True));
  let prefix =
    A.sub
      (V.vec_to_array b.bt_storage)
      #1.0R
      #(fun _ -> True)
      0sz
      (SZ.v current);
  with prefix_mask.
    assert (A.pts_to_mask prefix #1.0R prefix_mask (fun _ -> True));
  A.from_mask prefix;
  with prefix_bytes.
    assert (pts_to prefix prefix_bytes);
  assert (pure (Seq.equal
    prefix_bytes
    (Seq.slice raw 0 (SZ.v current))));
  Seq.lemma_eq_elim
    (pending (Ghost.reveal model))
    (Seq.slice raw 0 (SZ.v current));
  rewrite (pts_to prefix prefix_bytes) as
    (pts_to prefix (pending (Ghost.reveal model)));
  let view = {
    pv_parent = V.vec_to_array b.bt_storage;
    pv_data = prefix;
    pv_length = current;
    pv_raw_before = Ghost.hide raw;
  };
  assert (pure (view.pv_length == current));
  assert (pure (Ghost.reveal view.pv_raw_before == raw));
  fold (buffered_frame
    b
    {
      pv_parent = V.vec_to_array b.bt_storage;
      pv_data = prefix;
      pv_length = current;
      pv_raw_before = Ghost.hide raw;
    }
    (Ghost.reveal model)
    (Ghost.reveal received)
    (Ghost.reveal delivered)
    (Ghost.reveal sent));
  rewrite
    (buffered_frame
      b
      {
        pv_parent = V.vec_to_array b.bt_storage;
        pv_data = prefix;
        pv_length = filled;
        pv_raw_before = Ghost.hide raw;
      }
      (Ghost.reveal model)
      (Ghost.reveal received)
      (Ghost.reveal delivered)
      (Ghost.reveal sent))
    as
    (buffered_frame
      b
      view
      (Ghost.reveal model)
      (Ghost.reveal received)
      (Ghost.reveal delivered)
      (Ghost.reveal sent));
  rewrite
    (pts_to prefix (pending (Ghost.reveal model)))
    as
    (pts_to (view_data view) (pending (Ghost.reveal model)));
  view
}

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
{
  unfold (buffered_frame
    b
    view
    (Ghost.reveal model)
    (Ghost.reveal received)
    (Ghost.reveal delivered)
    (Ghost.reveal sent));
  with raw_mask.
    assert (
      TCP.is_channel
        b.bt_channel
        (Ghost.reveal received)
        (Ghost.reveal sent) **
      Box.pts_to b.bt_filled view.pv_length **
      A.pts_to_mask
        (V.vec_to_array b.bt_storage)
        #1.0R
        raw_mask
        (fun i -> True /\ ~(0 <= i /\ i < SZ.v view.pv_length)));
  A.to_mask view.pv_data;
  with prefix_mask.
    assert (A.pts_to_mask view.pv_data #1.0R prefix_mask (fun _ -> True));
  rewrite
    (A.pts_to_mask view.pv_data #1.0R prefix_mask (fun _ -> True))
    as
    (A.pts_to_mask
      (A.gsub
        view.pv_parent
        0
        (SZ.v view.pv_length))
      #1.0R
      prefix_mask
      (fun _ -> True));
  rewrite
    (A.pts_to_mask
      (A.gsub
        view.pv_parent
        0
        (SZ.v view.pv_length))
      #1.0R
      prefix_mask
      (fun _ -> True))
    as
    (A.pts_to_mask
      (A.gsub
        (V.vec_to_array b.bt_storage)
        0
        (SZ.v view.pv_length))
      #1.0R
      prefix_mask
      (fun _ -> True));
  A.return_sub
    (V.vec_to_array b.bt_storage)
    #1.0R
    #raw_mask
    #prefix_mask
    #(fun i -> True /\ ~(0 <= i /\ i < SZ.v view.pv_length))
    #(fun _ -> True)
    #0
    #(SZ.v view.pv_length);
  with joined_mask.
    assert (A.pts_to_mask
      (V.vec_to_array b.bt_storage)
      #1.0R
      joined_mask
      (fun i ->
        (True /\ ~(0 <= i /\ i < SZ.v view.pv_length)) \/
        (0 <= i /\ i < SZ.v view.pv_length /\ True)));
  assert (pure (forall (i:nat). i < Seq.length joined_mask ==>
    Seq.index joined_mask i ==
      (if i < SZ.v view.pv_length
       then Seq.index prefix_mask i
       else Seq.index raw_mask i)));
  lemma_rejoined_mask
    (Ghost.reveal view.pv_raw_before)
    (pending (Ghost.reveal model))
    raw_mask
    prefix_mask
    joined_mask
    (SZ.v view.pv_length);
  assert (pure (forall (i:nat). i < Seq.length joined_mask ==>
    Some? (Seq.index joined_mask i)));
  A.from_mask (V.vec_to_array b.bt_storage);
  with raw_after.
    assert (pts_to (V.vec_to_array b.bt_storage) raw_after);
  Seq.lemma_eq_intro raw_after (Ghost.reveal view.pv_raw_before);
  V.to_vec_pts_to b.bt_storage;
  fold (is_buffered
    b
    (Ghost.reveal model)
    (Ghost.reveal received)
    (Ghost.reveal delivered)
    (Ghost.reveal sent))
}

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
{
  unfold (is_buffered
    b
    (Ghost.reveal model)
    (Ghost.reveal received)
    (Ghost.reveal delivered)
    (Ghost.reveal sent));
  with raw filled.
    assert (
      TCP.is_channel
        b.bt_channel
        (Ghost.reveal received)
        (Ghost.reveal sent) **
      V.pts_to b.bt_storage #1.0R raw **
      Box.pts_to b.bt_filled filled);
  let current = Box.(!b.bt_filled);
  assert (pure (current == filled));
  assert (pure (Seq.length (pending (Ghost.reveal model)) == SZ.v current));
  V.to_array_pts_to b.bt_storage;
  let remaining =
    I.compact_buffer_suffix
      (V.vec_to_array b.bt_storage)
      b.bt_capacity
      current
      consumed;
  with raw_after.
    assert (pts_to (V.vec_to_array b.bt_storage) raw_after);
  Box.(b.bt_filled := remaining);
  V.to_vec_pts_to b.bt_storage;
  let model' : erased phys_buffer =
    Ghost.hide (compact (Ghost.reveal model) (SZ.v consumed));
  lemma_compact_wf (Ghost.reveal model) (SZ.v consumed);
  lemma_compact_pending (Ghost.reveal model) (SZ.v consumed);
  I.lemma_compact_capacity (Ghost.reveal model) (SZ.v consumed);
  lemma_commit_preserves_full
    (Ghost.reveal received)
    (Ghost.reveal delivered)
    (Ghost.reveal model)
    (SZ.v consumed);
  SeqP.slice_slice
    raw
    0
    (SZ.v current)
    (SZ.v consumed)
    (SZ.v current);
  assert (pure (Seq.equal
    (Seq.slice raw_after 0 (SZ.v remaining))
    (pending (Ghost.reveal model'))));
  fold (is_buffered
    b
    (Ghost.reveal model')
    (Ghost.reveal received)
    (committed_after
      (Ghost.reveal delivered)
      (Ghost.reveal model)
      (SZ.v consumed))
    (Ghost.reveal sent));
  remaining
}

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
{
  unfold (is_buffered
    b
    (Ghost.reveal model)
    (Ghost.reveal received)
    (Ghost.reveal delivered)
    (Ghost.reveal sent));
  with raw filled.
    assert (
      TCP.is_channel
        b.bt_channel
        (Ghost.reveal received)
        (Ghost.reveal sent) **
      V.pts_to b.bt_storage #1.0R raw **
      Box.pts_to b.bt_filled filled);
  let current = Box.(!b.bt_filled);
  assert (pure (current == filled));
  assert (pure (Seq.length (pending (Ghost.reveal model)) == SZ.v current));
  assert (pure (SZ.v current < SZ.v b.bt_capacity));
  V.to_array_pts_to b.bt_storage;
  let read_result =
    I.read_append
      b.bt_channel
      (V.vec_to_array b.bt_storage)
      b.bt_capacity
      current;
  with raw_after chunk.
    assert (
      TCP.is_channel
        b.bt_channel
        (Seq.append (Ghost.reveal received) chunk)
        (Ghost.reveal sent) **
      pts_to (V.vec_to_array b.bt_storage) raw_after);
  let read_len = I.read_count read_result;
  let new_filled = I.total_count read_result;
  Box.(b.bt_filled := new_filled);
  V.to_vec_pts_to b.bt_storage;
  let model' : erased phys_buffer =
    Ghost.hide (append_read (Ghost.reveal model) chunk);
  lemma_append_read_wf (Ghost.reveal model) chunk;
  lemma_append_read_capacity (Ghost.reveal model) chunk;
  lemma_append_read_pending (Ghost.reveal model) chunk;
  lemma_append_read_extends_received
    (Ghost.reveal received)
    (Ghost.reveal delivered)
    (Ghost.reveal model)
    chunk;
  assert (pure (Seq.equal
    (Seq.slice raw_after 0 (SZ.v new_filled))
    (pending (Ghost.reveal model'))));
  fold (is_buffered
    b
    (Ghost.reveal model')
    (Seq.append (Ghost.reveal received) chunk)
    (Ghost.reveal delivered)
    (Ghost.reveal sent));
  read_len
}

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
{
  unfold (is_buffered
    b
    (Ghost.reveal model)
    (Ghost.reveal received)
    (Ghost.reveal delivered)
    (Ghost.reveal sent));
  with raw filled.
    assert (
      TCP.is_channel
        b.bt_channel
        (Ghost.reveal received)
        (Ghost.reveal sent) **
      V.pts_to b.bt_storage #1.0R raw **
      Box.pts_to b.bt_filled filled);
  let written = TCP.write b.bt_channel data len;
  assert (pure (written == len));
  fold (is_buffered
    b
    (Ghost.reveal model)
    (Ghost.reveal received)
    (Ghost.reveal delivered)
    (Seq.append
      (Ghost.reveal sent)
      (if SZ.v written <= Seq.length (Ghost.reveal 'bytes)
       then Seq.slice (Ghost.reveal 'bytes) 0 (SZ.v written)
       else Seq.create 0 0uy)));
  written
}

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
{
  let storage = close_detach b;
  with model'.
    assert (is_storage storage model');
  free_storage storage
}
