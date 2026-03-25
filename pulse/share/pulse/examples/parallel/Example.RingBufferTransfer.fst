module Example.RingBufferTransfer
open Pulse
#lang-pulse
open Pulse.Lib.Pervasives
open FStar.Preorder
module RB = Pulse.Lib.RingBuffer
module MR = Pulse.Lib.MonotonicGhostRef
module GR = Pulse.Lib.GhostReference
module R = FStar.ReflexiveTransitiveClosure
module L = Pulse.Lib.SpinLock
let as_prop (p:Type) = p <==> True

[@@erasable]
noeq
type stream (t:Type0) = {
  messages: FStar.Seq.seq t;
  read_position: i:nat { i <= Seq.length messages };
}

let empty_stream #t : stream t = { messages = Seq.empty; read_position = 0 }

noeq
type action (t:Type0) =
| Send of t
| Receive of t

let send (#t:Type0) (m:t) (s0:stream t): stream t = { s0 with messages = Seq.snoc s0.messages m }

let recv (#t:Type0) (s0:stream t) : GTot (option (t & stream t)) =
  if s0.read_position < Seq.length s0.messages 
  then Some (Seq.index s0.messages s0.read_position, { s0 with read_position = s0.read_position + 1 })
  else None

let receive (#t:Type0) (m:t) (s0:stream t) : stream t = snd (Some?.v (recv (send m s0)))

let action_step (#t:Type0) (a:action t) (s0:stream t) (s1:stream t) : prop =
  match a with
  | Send m ->
    s1 == send m s0
  | Receive m ->
    match recv s0 with
    | None -> False
    | Some (m', s1') -> m == m' /\ s1 == s1'

let step (#t:Type0) (s0 s1:stream t) : prop = exists (a:action t). action_step #t a s0 s1
let is_prefix #t : preorder (Seq.seq t) = fun s0 s1 ->
  Seq.length s0 <= Seq.length s1 /\
  Seq.slice s1 0 (Seq.length s0) `Seq.equal` s0
let is_suffix_of #t (sfx s:Seq.seq t) : prop =
  Seq.length sfx <= Seq.length s /\
  Seq.slice s (Seq.length s - Seq.length sfx) (Seq.length s) `Seq.equal` sfx

let suffix_of_reflexive #t (s:Seq.seq t) 
: Lemma (s `is_suffix_of` s) = 
  assert (Seq.append (Seq.empty) s `Seq.equal` s)

let stream_evolves (#t:Type0) : preorder (stream t) = fun s0 s1 ->
  R.closure (step #t) s0 s1 /\
  is_prefix s0.messages s1.messages /\ //strengthened to make the proof of the main lemma easier
  s0.read_position <= s1.read_position //strengthened to make the proof of the main lemma easier

let stream_evolves_send #t (s0:stream t) (m:t)
: Lemma (ensures stream_evolves #t s0 (send m s0))
        [SMTPat (stream_evolves #t s0 (send m s0))]
= assert (action_step #t (Send m) s0 (send m s0));
  R.closure_step (step #t) s0 (send m s0)

let incr_recv_position #t (s0:stream t{ s0.read_position < Seq.length s0.messages }) =
  { s0 with read_position = s0.read_position + 1 }

let stream_evolves_recv #t (s0:stream t)
  : Lemma 
    (requires s0.read_position < Seq.length s0.messages)
    (ensures stream_evolves #t s0 (incr_recv_position s0))
    [SMTPat (stream_evolves #t s0 (incr_recv_position s0))]
  = assert (action_step #t (Receive (Seq.index s0.messages s0.read_position)) s0 (incr_recv_position s0));
    R.closure_step (step #t) s0 (incr_recv_position s0)

noeq
type chan (t:Type0) = {
  capacity: c:erased nat {c > 0}; //the capacity of the ring buffer, ghostly
  buffer: RB.ringbuffer t; //the actual ring buffer
  stream: MR.mref (stream_evolves #t);   //the entire stream, ghostly
  read_position: GR.ref nat; //the current read position in the stream, ghostly
  write_position: GR.ref nat; //the current write position in the stream, ghostly
}

let stream_exactly #t (c:chan t) (s:stream t) = MR.pts_to c.stream #1.0R s
let stream_snapshot #t (c:chan t) (s:stream t) = MR.snapshot c.stream s

[@@pulse_unfold]
let channel_exactly #t ([@@@mkey] c:chan t) (s:stream t) =
    stream_exactly c s ** //the ghost stream points exactly to s
    GR.pts_to c.read_position #0.5R s.read_position ** //1/2 permission to the read position, agrees with s.read_position
    GR.pts_to c.write_position #0.5R (Seq.length s.messages) ** //1/2 permission to the write position, agrees with s.read_position
    (exists* suffix. 
        RB.is_ringbuffer c.buffer suffix c.capacity //the buffer contains a suffix of the messages in s, with capacity c.capacity
      ** pure (
        suffix `is_suffix_of` s.messages /\
        s.read_position == Seq.length s.messages - Seq.length suffix //the read position is exactly at the next message to be read
      ) //and that suffix is indeed a suffix of s.messages
    )


noeq
type channel (t:Type0) = {
  ch:chan t;
  l:L.lock;
}

let channel_perm #f (#t:Type0) (c:channel t) =
  L.lock_alive c.l #f (exists* s. channel_exactly c.ch s)

let reader_state (#t:Type0) (c:channel t) (s:stream t) =
  exists* (s':stream t). 
    stream_snapshot c.ch s' ** //knowledge of a stable snapshot
    GR.pts_to c.ch.read_position #0.5R s.read_position ** //and 1/2 perm on the current read position
    pure (s.messages `is_prefix` s'.messages /\ //and that snapshot's messages are an extension of the reader's current view
          s.read_position == Seq.length s.messages /\
          eq2 #nat s.read_position s'.read_position) //and everything in the reader's view has been read already

let writer_state (#t:Type0) (c:channel t) (s:stream t) =
  stream_snapshot c.ch s ** //knowledge of a stable snapshot
  GR.pts_to c.ch.write_position #0.5R (Seq.length s.messages) //1/2 perm on the full stream

ghost
fn writer_has_full_knowledge_of_messages (#t:Type0) (c:channel t) (s s':stream t)
  preserves writer_state c s
  preserves GR.pts_to c.ch.write_position #0.5R (Seq.length s'.messages)
  preserves stream_exactly c.ch s'
  ensures pure (s.messages == s'.messages)
{
  unfold writer_state;
  unfold stream_exactly;
  unfold stream_snapshot;
  MR.recall_snapshot _;
  GR.pts_to_injective_eq c.ch.write_position;
  assert pure (Seq.equal s.messages s'.messages);
  fold stream_snapshot;
  fold stream_exactly;
  fold writer_state;
}

ghost
fn reader_has_knowledge_of_prefix (#t:Type0) (c:channel t) (s s':stream t)
  preserves reader_state c s
  preserves exists* n. GR.pts_to c.ch.read_position #0.5R n ** pure (n == s'.read_position)
  preserves stream_exactly c.ch s'
  ensures pure (s.messages `is_prefix` s'.messages)
  ensures pure (eq2 #nat s.read_position s'.read_position)
{
  unfold reader_state;
  unfold stream_exactly;
  unfold stream_snapshot;
  MR.recall_snapshot _;
  GR.pts_to_injective_eq c.ch.read_position;
  fold stream_snapshot;
  fold stream_exactly;
  fold reader_state;
}

module SZ = FStar.SizeT

fn create_channel (#t:Type0) (capacity:SZ.t{SZ.v capacity > 0}) (init:t)
  returns c:channel t
  ensures channel_perm #0.5R c
  ensures channel_perm #0.5R c
  ensures reader_state c empty_stream
  ensures writer_state c empty_stream
{
  let buffer = RB.create capacity init;
  let stream_ref = MR.alloc #_ #(stream_evolves #t) (empty_stream #t);
  let read_pos = GR.alloc (0<:nat);
  let write_pos = GR.alloc (0<:nat);
  let ch = { 
    capacity=SZ.v capacity; 
    buffer;
    stream = stream_ref;
    read_position = read_pos;
    write_position = write_pos 
  };
  rewrite each 
    stream_ref as ch.stream, 
    read_pos as ch.read_position,
    write_pos as ch.write_position, 
    buffer as ch.buffer;
  MR.take_snapshot ch.stream _;
  dup (MR.snapshot ch.stream (empty_stream #t)) ();
  fold (stream_snapshot ch (empty_stream #t));
  fold (stream_snapshot ch (empty_stream #t));
  fold (stream_exactly ch (empty_stream #t));
  GR.share ch.read_position;
  GR.share ch.write_position;
  suffix_of_reflexive (empty_stream #t).messages;
  let lock = L.new_lock (exists* s. channel_exactly ch s);
  let c = { ch; l = lock };
  rewrite each ch as c.ch, lock as c.l;
  L.share c.l;
  fold (reader_state c (empty_stream #t));
  fold (writer_state c (empty_stream #t));
  fold (channel_perm #0.5R c);
  fold (channel_perm #0.5R c);
  c
}

fn destroy_channel_lock (#t:Type0) (c:channel t)
  requires channel_perm #0.5R c ** channel_perm #0.5R c
  ensures exists* s. channel_exactly c.ch s
{
  unfold channel_perm;
  unfold channel_perm;
  L.gather c.l;
  L.acquire c.l;
  L.free c.l;
}

fn destroy_channel #t (c:channel t)
requires exists* s. channel_exactly c.ch s
ensures emp
{
  RB.free c.ch.buffer;
  drop_ (GR.pts_to c.ch.read_position #0.5R _);
  drop_ (GR.pts_to c.ch.write_position #0.5R _);
  drop_ (stream_exactly c.ch _);
}

fn rec write (#t:Type) (c:channel t) (m:t) (#s:stream t)
  preserves channel_perm #0.5R c
  requires writer_state c s
  ensures exists* s'. writer_state c s' ** pure (s'.messages == (send m s).messages)
{
  unfold channel_perm;
  L.acquire c.l;
  let ok = RB.push_back c.ch.buffer m;
  if not ok
  { //no space left; recurse to retry
    L.release c.l;
    fold channel_perm;
    write c m #s
  }
  else
  {
    writer_has_full_knowledge_of_messages c _ _;
    unfold writer_state;
    with s'. assert (stream_exactly c.ch s');
    unfold stream_exactly;
    GR.gather c.ch.write_position;
    GR.write c.ch.write_position (Seq.length s.messages + 1);
    GR.share c.ch.write_position;
    MR.update c.ch.stream (send m s');
    MR.take_snapshot c.ch.stream _;
    drop_ (stream_snapshot c.ch s);
    fold (stream_snapshot c.ch (send m s'));
    fold (writer_state c (send m s'));
    fold stream_exactly;
    L.release c.l;
    fold channel_perm;
  }
}

fn rec read (#t:Type) (c:channel t) (#s:stream t)
  preserves channel_perm #0.5R c
  requires reader_state c s
  returns m:t
  ensures exists* s'. reader_state c s' ** pure (s' == receive m s)
  
{
  unfold channel_perm;
  L.acquire c.l;
  if RB.is_empty c.ch.buffer
  { //no messages to read; recurse to retry
    L.release c.l;
    fold channel_perm;
    read c #s
  }
  else
  {
    let m = RB.peek_front c.ch.buffer;
    RB.pop_front c.ch.buffer;
    reader_has_knowledge_of_prefix c _ _;
    unfold reader_state;
    with s'. assert (stream_exactly c.ch s');
    unfold stream_exactly;
    GR.gather c.ch.read_position;
    GR.write c.ch.read_position (s.read_position + 1);
    GR.share c.ch.read_position;
    MR.update c.ch.stream (incr_recv_position s');
    MR.take_snapshot c.ch.stream _;
    drop_ (stream_snapshot c.ch _);
    fold (stream_snapshot c.ch (incr_recv_position s'));
    fold (reader_state c (receive m s));
    fold stream_exactly;
    L.release c.l;
    fold channel_perm;
    m
  }
}


ghost
fn reader_writer_agree_on_prefix (#t:Type0) (c:channel t) (s0 s1 s2:stream t)
  preserves reader_state c s0
  preserves writer_state c s1
  preserves channel_exactly c.ch s2
  ensures pure (s0.messages `is_prefix` s1.messages /\ s1.messages == s2.messages)
{
  reader_has_knowledge_of_prefix c _ _;
  writer_has_full_knowledge_of_messages c _ _;
}

ghost
fn reader_writer_related (#t:Type0) (c:channel t) (s0 s1:stream t)
  preserves reader_state c s0
  preserves writer_state c s1
  ensures pure (
    //this is weaker than desired
    //ideally we should be able to show without further assumptions that
    //that only the LHS of the disjunct below is true
    //For that, we would probably need to move to the Anchored preorders
    //and prove that the write_state holds the anchor and so is
    //always up to date... but that's for another revision
    s0.messages `is_prefix` s1.messages \/
    s1.messages `is_prefix` s0.messages
  )
{
  unfold reader_state;
  with s0'. assert (stream_snapshot c.ch s0');
  unfold stream_snapshot;
  unfold writer_state;
  unfold stream_snapshot;
  MR.snapshots_related c.ch.stream #s0' #s1;
  fold (stream_snapshot c.ch s1);
  fold writer_state;
  fold (stream_snapshot c.ch s0');
  fold reader_state;
}

///////////////////////////////////////////////////////////
//A test program
//Shows that you can create a channel,
//spawn a reader and writer in parallel, and they will agree on the stream of messages
///////////////////////////////////////////////////////////

let is_id_seq_len (s:Seq.seq nat) (n:nat) : prop =
  Seq.length s == n /\
  (forall (i:nat { i < n }). Seq.index s i == i)

fn writer (c:channel nat)
  preserves channel_perm #0.5R c
  requires writer_state c empty_stream
  ensures exists* s'. writer_state c s' **
    pure (is_id_seq_len s'.messages 50)
{
  let mut i : nat = 0;
  while (!i < 50)
  invariant live i
  invariant (exists* s. writer_state c s ** pure (is_id_seq_len s.messages !i))
  invariant pure (!i <= 50)
  {
    write c !i;
    i := !i + 1;
  };
}

fn reader (c:channel nat)
  preserves channel_perm #0.5R c
  requires reader_state c empty_stream
  ensures exists* s'. reader_state c s' ** pure (Seq.length s'.messages == 50)
{
  let mut i : nat = 0;
  while (!i < 50)
  invariant live i
  invariant (exists* s. reader_state c s ** pure (Seq.length s.messages == !i))
  invariant pure (!i <= 50)
  {
    let _ = read c;
    i := !i + 1;
  };
}

//assume a primitive to spawn two threads in parallel and joining, similar to Pulse.Lib.Par
fn par (#preL: slprop) #postL #preR #postR
  (f:unit -> stt unit preL (fun _ -> postL))
  (g:unit -> stt unit preR (fun _ -> postR))
  requires preL
  requires preR
  ensures postL
  ensures postR
{ admit() }

fn main ()
{
  let c = create_channel #nat 10sz 0; //create a channel with capacity 10
  par (fun _ -> reader c) (fun _ -> writer c); //spawn a reader and writer in parallel; and wait for them to join
  destroy_channel_lock c; //destroy the channel, ensuring all resources are cleaned up
  reader_writer_agree_on_prefix c _ _ _; //at this point we can prove using this ghost function
  assert (exists* s0 s1.  //that the reader and writer agree on the entire stream of messages
    reader_state c s0 **
    writer_state c s1 ** 
    pure (Seq.equal s0.messages s1.messages)); //and that stream contains exactly the messages we expect
  //free up rest
  destroy_channel c;
  drop_ (reader_state c _);
  drop_ (writer_state c _);
}