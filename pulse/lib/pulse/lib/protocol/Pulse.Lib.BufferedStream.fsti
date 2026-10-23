module Pulse.Lib.BufferedStream

#lang-pulse

(**

  Protocol-independent scheduling / read-authorisation layer for a buffered
  stream, built on top of [Pulse.Lib.BufferedTCP].  It has two layers.

  Layer 1 (the pure classifier model) lives in
  [Pulse.Lib.BufferedStream.Classifier], which this module includes.

  ---------------------------------------------------------------------------
  Layer 2 — the RELATIONAL adapter (for effectful endpoints, e.g. TLS 1.3).
  ---------------------------------------------------------------------------

  TLS has NO pure pre-classifier: its receive step is an effectful, relational
  process that mutates connection/crypto state and returns a status
  ([StepOk]/[NeedMoreInput]/errors) plus a consumed length.  To model this
  honestly, [buffered_stream_endpoint] is a Pulse class in which:

    * [bse_owns e st received committed b] is the endpoint's *linear* stream
      ownership (an [slprop]); linearity is genuine — it is the caller's
      non-duplicable resources.  It fixes the exact current state [st], the exact
      full received transport history [received], the committed prefix and the
      physical buffer [b], with [received == committed ++ pending b] as the real
      invariant ([bse_owns_wf]).

    * [bse_terminal e st received] is terminal ownership after a fatal (Reject)
      decision — the endpoint is done (matches TLS [ConnectionFailed]).

    * [bse_read_auth e st received committed b] is an endpoint-defined,
      exclusive *read-ready ownership state*.  It contains the live endpoint
      resources, including the concrete channel and backing array; it is not a
      detached token indexed only by byte values.

    * [bse_process] classifies the current pending RELATIONALLY, threading the
      received history UNCHANGED through the live cases (processing does not read
      the network). [bse_result_valid] retains the endpoint-specific correctness
      theorem for the returned result across the generic loop. NeedMore is an
      *exact stutter* — it transitions exclusive live ownership to [bse_read_auth]
      only when the buffer still has free space ([BT.free_space b' > 0]); if the
      buffer is FULL it instead goes to [bse_buffer_full] (a scheduler failure)
      and NEVER yields read authorisation (no zero-length reads).  Progress/Yield
      stay live and advance committed/buffer (must process again); Reject goes
      terminal.

    * [bse_read] consumes the authorisation and the live ownership, reads a chunk,
      and re-establishes live ownership at the advanced history
      [received' = received ++ chunk] and the append-read buffer.

   [drive_until_conclusive] also returns the unused read fuel, so callers can
   thread one explicit workflow budget through buffering and protocol progress.

  The module depends on [Pulse.Lib.BufferedTCP] and never the reverse.

**)


open Pulse.Lib.Pervasives

module Seq = FStar.Seq
module SZ  = FStar.SizeT
module TCP = Pulse.Lib.TCP
module BT  = Pulse.Lib.BufferedTCP

include Pulse.Lib.BufferedStream.Classifier

type process_outcome (output error result:Type0) =
  | Processed :
      result ->
      classification output error ->
      process_outcome output error result
  | ProcessBufferFull :
      result ->
      process_outcome output error result

type drive_outcome (output error result:Type0) =
  | DriveProgress :
      result ->
      SZ.t ->
      SZ.t ->
      drive_outcome output error result
  | DriveYield :
      result ->
      SZ.t ->
      output ->
      SZ.t ->
      drive_outcome output error result
  | DriveReject :
      result ->
      error ->
      FStar.SizeT.t ->
      drive_outcome output error result
  | DriveBufferFull :
      result ->
      FStar.SizeT.t ->
      drive_outcome output error result
  | DriveExhausted :
      drive_outcome output error result

let drive_fuel_left
  (#output #error #result:Type0)
  (outcome:drive_outcome output error result)
  : FStar.SizeT.t =
  match outcome with
  | DriveProgress _ _ fuel_left
  | DriveYield _ _ _ fuel_left
  | DriveReject _ _ fuel_left
  | DriveBufferFull _ fuel_left ->
    fuel_left
  | DriveExhausted ->
    0sz

let process_transition
  (#output #error:Type0)
  (d:classification output error)
  (committed committed':TCP.bytes)
  (b b':BT.phys_buffer)
  : prop =
  match d with
  | NeedMore ->
    Seq.equal committed' committed /\ b' == b
  | Reject _ ->
    True
  | Progress k ->
    0 < SZ.v k /\ SZ.v k <= Seq.length (BT.pending b) /\
    Seq.equal committed' (BT.committed_after committed b (SZ.v k)) /\
    b' == BT.compact b (SZ.v k)
  | Yield k _ ->
    0 < SZ.v k /\ SZ.v k <= Seq.length (BT.pending b) /\
    Seq.equal committed' (BT.committed_after committed b (SZ.v k)) /\
    b' == BT.compact b (SZ.v k)

let read_delivers
  (received received':TCP.bytes)
  (b b':BT.phys_buffer)
  : prop =
  BT.buffer_wf b' /\
  BT.capacity b' == BT.capacity b /\
  (exists (chunk:TCP.bytes).
     BT.chunk_fits b chunk /\
     Seq.equal (BT.pending b') (Seq.append (BT.pending b) chunk) /\
     Seq.equal received' (Seq.append received chunk))

noextract
let process_post
  (#endpoint #state #output #error #result:Type0)
  (decide:result -> GTot (classification output error))
  (needs_more:state -> TCP.bytes -> prop)
  (result_valid:endpoint -> state -> result -> state -> prop)
  (owns:endpoint -> state -> TCP.bytes -> TCP.bytes -> BT.phys_buffer -> slprop)
  (terminal:endpoint -> state -> TCP.bytes -> slprop)
  (buffer_full:endpoint -> state -> TCP.bytes -> slprop)
  (read_auth:endpoint -> state -> TCP.bytes -> TCP.bytes -> BT.phys_buffer -> slprop)
  (e:endpoint)
  (st:state)
  (received committed:TCP.bytes)
  (b:BT.phys_buffer)
  (outcome:process_outcome output error result)
  : slprop =
  match outcome with
  | ProcessBufferFull r ->
    exists* st' committed' b'.
      buffer_full e st' received **
      pure (
        decide r == NeedMore /\
        result_valid e st r st' /\
        needs_more st (BT.pending b) /\
        process_transition
          (decide r)
          committed
          committed'
          b
          b' /\
        st' == st /\
        BT.free_space b == 0)
  | Processed r decision ->
    match decision with
    | Reject _ ->
      exists* st' received'.
        terminal e st' received' **
        pure (
          decision == decide r /\
          result_valid e st r st')
    | NeedMore ->
      exists* st' committed' b'.
        read_auth e st' received committed' b' **
        pure (
          decision == decide r /\
          result_valid e st r st' /\
          needs_more st (BT.pending b) /\
          process_transition
            decision
            committed
            committed'
            b
            b' /\
          st' == st /\
          BT.can_read b)
    | Progress _ ->
      exists* st' committed' b'.
        owns e st' received committed' b' **
        pure (
          decision == decide r /\
          result_valid e st r st' /\
          process_transition
            decision
            committed
            committed'
            b
            b')
    | Yield _ _ ->
      exists* st' committed' b'.
        owns e st' received committed' b' **
        pure (
          decision == decide r /\
          result_valid e st r st' /\
          process_transition
            decision
            committed
            committed'
            b
            b')

noextract
class buffered_stream_endpoint
  (endpoint:Type0)
  (state:Type0)
  (output:Type0)
  (error:Type0)
  (result:Type0)
  =
{
  bse_decide:
    result -> GTot (classification output error);

  bse_needs_more:
    state -> TCP.bytes -> prop;

  bse_result_valid:
    endpoint -> before:state -> result -> after:state -> prop;

  bse_owns:
    endpoint -> state -> TCP.bytes -> TCP.bytes -> BT.phys_buffer -> slprop;

  bse_terminal:
    endpoint -> state -> TCP.bytes -> slprop;

  bse_buffer_full:
    endpoint -> state -> TCP.bytes -> slprop;

  bse_read_auth:
    endpoint -> state -> TCP.bytes -> TCP.bytes -> BT.phys_buffer -> slprop;

  bse_owns_wf:
    e:endpoint ->
    st:Ghost.erased state ->
    received:Ghost.erased TCP.bytes ->
    committed:Ghost.erased TCP.bytes ->
    b:Ghost.erased BT.phys_buffer ->
      stt_ghost unit emp_inames
        (bse_owns
          e
          (Ghost.reveal st)
          (Ghost.reveal received)
          (Ghost.reveal committed)
          (Ghost.reveal b))
        (fun _ ->
          bse_owns
            e
            (Ghost.reveal st)
            (Ghost.reveal received)
            (Ghost.reveal committed)
            (Ghost.reveal b) **
          pure (
            BT.buffer_wf (Ghost.reveal b) /\
            BT.received_split
              (Ghost.reveal received)
              (Ghost.reveal committed)
              (Ghost.reveal b)));

  bse_process:
    e:endpoint ->
    st:Ghost.erased state ->
    received:Ghost.erased TCP.bytes ->
    committed:Ghost.erased TCP.bytes ->
    b:Ghost.erased BT.phys_buffer ->
      stt (process_outcome output error result)
        (bse_owns
          e
          (Ghost.reveal st)
          (Ghost.reveal received)
          (Ghost.reveal committed)
          (Ghost.reveal b))
        (fun outcome ->
          process_post
            bse_decide
            bse_needs_more
            bse_result_valid
            bse_owns
            bse_terminal
            bse_buffer_full
            bse_read_auth
            e
            (Ghost.reveal st)
            (Ghost.reveal received)
            (Ghost.reveal committed)
            (Ghost.reveal b)
            outcome);

  bse_read:
    e:endpoint ->
    st:Ghost.erased state ->
    received:Ghost.erased TCP.bytes ->
    committed:Ghost.erased TCP.bytes ->
    b:Ghost.erased BT.phys_buffer ->
      stt unit
        (bse_read_auth
           e
           (Ghost.reveal st)
           (Ghost.reveal received)
           (Ghost.reveal committed)
           (Ghost.reveal b) **
         pure (
           BT.buffer_wf (Ghost.reveal b) /\
           BT.can_read (Ghost.reveal b) /\
           bse_needs_more
             (Ghost.reveal st)
             (BT.pending (Ghost.reveal b))))
        (fun _ ->
          exists* received' b'.
            bse_owns
              e
              (Ghost.reveal st)
              received'
              (Ghost.reveal committed)
              b' **
            pure (
              read_delivers
                (Ghost.reveal received)
                received'
                (Ghost.reveal b)
                b'));
}

noextract
let drive_post
  (#endpoint #state #output #error #result:Type0)
  (ep:buffered_stream_endpoint endpoint state output error result)
  (e:endpoint)
  (initial:state)
  (outcome:drive_outcome output error result)
  : slprop =
  match outcome with
  | DriveExhausted ->
    exists* st' received' committed' b'.
      ep.bse_owns e st' received' committed' b' **
      pure (st' == initial)
  | DriveBufferFull r _ ->
    exists* st' received'.
      ep.bse_buffer_full e st' received' **
      pure (ep.bse_result_valid e initial r st')
  | DriveProgress r consumed _ ->
    exists* st' received' committed' b'.
      ep.bse_owns e st' received' committed' b' **
      pure (
        ep.bse_decide r == Progress consumed /\
        ep.bse_result_valid e initial r st')
  | DriveYield r consumed output _ ->
    exists* st' received' committed' b'.
      ep.bse_owns e st' received' committed' b' **
      pure (
        ep.bse_decide r == Yield consumed output /\
        ep.bse_result_valid e initial r st')
  | DriveReject r error _ ->
    exists* st' received'.
      ep.bse_terminal e st' received' **
      pure (
        ep.bse_decide r == Reject error /\
        ep.bse_result_valid e initial r st')

inline_for_extraction noextract
fn drive_until_conclusive
  (#endpoint #state #output #error #result:Type0)
  (ep:buffered_stream_endpoint endpoint state output error result)
  (process:(
    e0:endpoint ->
    st0:Ghost.erased state ->
    received0:Ghost.erased TCP.bytes ->
    committed0:Ghost.erased TCP.bytes ->
    b0:Ghost.erased BT.phys_buffer ->
      stt (process_outcome output error result)
        (ep.bse_owns
          e0
          (Ghost.reveal st0)
          (Ghost.reveal received0)
          (Ghost.reveal committed0)
          (Ghost.reveal b0))
        (fun process_result ->
          process_post
            ep.bse_decide
            ep.bse_needs_more
            ep.bse_result_valid
            ep.bse_owns
            ep.bse_terminal
            ep.bse_buffer_full
            ep.bse_read_auth
            e0
            (Ghost.reveal st0)
            (Ghost.reveal received0)
            (Ghost.reveal committed0)
            (Ghost.reveal b0)
            process_result)))
  (read:(
    e0:endpoint ->
    st0:Ghost.erased state ->
    received0:Ghost.erased TCP.bytes ->
    committed0:Ghost.erased TCP.bytes ->
    b0:Ghost.erased BT.phys_buffer ->
      stt unit
        (ep.bse_read_auth
           e0
           (Ghost.reveal st0)
           (Ghost.reveal received0)
           (Ghost.reveal committed0)
           (Ghost.reveal b0) **
         pure (
           BT.buffer_wf (Ghost.reveal b0) /\
           BT.can_read (Ghost.reveal b0) /\
           ep.bse_needs_more
             (Ghost.reveal st0)
             (BT.pending (Ghost.reveal b0))))
        (fun _ ->
          exists* received1 b1.
            ep.bse_owns
              e0
              (Ghost.reveal st0)
              received1
              (Ghost.reveal committed0)
              b1 **
            pure (
              read_delivers
                (Ghost.reveal received0)
                received1
                (Ghost.reveal b0)
                b1))))
  (e:endpoint)
  (st:Ghost.erased state)
  (received:Ghost.erased TCP.bytes)
  (committed:Ghost.erased TCP.bytes)
  (b:Ghost.erased BT.phys_buffer)
  (fuel:FStar.SizeT.t)
  requires
    ep.bse_owns
      e
      (Ghost.reveal st)
      (Ghost.reveal received)
      (Ghost.reveal committed)
      (Ghost.reveal b)
  returns outcome:drive_outcome output error result
  ensures
    drive_post ep e (Ghost.reveal st) outcome **
    pure (
      FStar.SizeT.v (drive_fuel_left outcome) <=
        FStar.SizeT.v fuel)
