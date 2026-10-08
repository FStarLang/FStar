module Pulse.Lib.BufferedStream

#lang-pulse

open Pulse.Lib.Pervasives

module Seq = FStar.Seq
module SZ  = FStar.SizeT
module TCP = Pulse.Lib.TCP
module BT  = Pulse.Lib.BufferedTCP

open Pulse.Lib.BufferedStream.Classifier

(* ================================================================== *)
(*  Layer 2: relational post-processing adapter (effectful endpoints) *)
(* ================================================================== *)

(**
  The buffer transition induced by a relational decision.  This does NOT assume a
  pure classifier: it relates a *decision value* [d] (obtained by actually
  running an effectful process step) to the committed/buffer transition.

    - [NeedMore] and [Reject] are exact stutters (no consumption);
    - [Progress]/[Yield] commit [consumed] pending bytes via the
      [Pulse.Lib.BufferedTCP] [committed_after]/[compact] model, with the
      consumption positive and bounded by the live count.
**)
(** The NeedMore case of a relational process is an exact stutter, consuming 0. *)
let lemma_process_transition_needmore_stutter
  (#output #error:Type0)
  (d:classification output error)
  (committed committed':TCP.bytes)
  (b b':BT.phys_buffer)
  : Lemma
      (requires process_transition d committed committed' b b' /\ d == NeedMore)
      (ensures
        Seq.equal committed' committed /\ b' == b /\ consumed_of d == 0sz)
= ()

(**
  A *live* relational process step (NeedMore / Progress / Yield) preserves the
  transport invariant.  The received stream is unchanged — processing consumes
  from the pending region, it does not read the network — while the
  committed/pending boundary moves for the progress cases.  (Reject is terminal
  and handled separately; it is excluded here.)
**)
let lemma_process_transition_preserves
  (#output #error:Type0)
  (d:classification output error)
  (received committed committed':TCP.bytes)
  (b b':BT.phys_buffer)
  : Lemma
      (requires
        process_transition d committed committed' b b' /\
        ~(Reject? d) /\
        BT.received_split received committed b /\
        BT.buffer_wf b)
      (ensures
        BT.received_split received committed' b' /\ BT.buffer_wf b')
= match d with
  | NeedMore -> ()
  | Reject _ -> ()
  | Progress k ->
    BT.lemma_commit_preserves_full received committed b (SZ.v k);
    BT.lemma_compact_wf b (SZ.v k)
  | Yield k _ ->
    BT.lemma_commit_preserves_full received committed b (SZ.v k);
    BT.lemma_compact_wf b (SZ.v k)

(**
  A read step extends the received stream by exactly the delivered chunk, keeping
  the [received = committed ++ pending] invariant (committed is unchanged).
**)
let lemma_read_extends_received
  (received committed:TCP.bytes)
  (b:BT.phys_buffer)
  (chunk:TCP.bytes)
  (b':BT.phys_buffer)
  : Lemma
      (requires
        BT.received_split received committed b /\
        BT.buffer_wf b /\
        BT.chunk_fits b chunk /\
        b' == BT.append_read b chunk)
      (ensures
        BT.received_split (Seq.append received chunk) committed b' /\
        BT.buffer_wf b')
= BT.lemma_append_read_extends_received received committed b chunk;
  BT.lemma_append_read_wf b chunk

(**
  The endpoint-level post of a read step: the result buffer [b'] is well-formed,
  of the same fixed capacity, its dense pending region is the old pending
  followed by the delivered chunk, AND the exact received history advances by
  that SAME chunk ([received' = received ++ chunk]).  The chunk is a squashed
  existential, so the Pulse existentials in [bse_read] stay inferable.  It is
  stated on the *pending* (the transport-observable dense prefix), not the full
  physical array, so it is realised by the real [Pulse.Lib.BufferedTCP.read_append]
  primitive, not only the canonical [append_read] model.
**)
(** [read_delivers] holds after appending any fitting chunk (canonical model). *)
let lemma_read_delivers_intro
  (received:TCP.bytes)
  (b:BT.phys_buffer)
  (chunk:TCP.bytes)
  : Lemma
      (requires BT.buffer_wf b /\ BT.chunk_fits b chunk)
      (ensures read_delivers received (Seq.append received chunk) b (BT.append_read b chunk))
= BT.lemma_append_read_wf b chunk;
  BT.lemma_append_read_capacity b chunk;
  BT.lemma_append_read_pending b chunk;
  introduce exists (c:TCP.bytes).
      BT.chunk_fits b c /\
      Seq.equal (BT.pending (BT.append_read b chunk)) (Seq.append (BT.pending b) c) /\
      Seq.equal (Seq.append received chunk) (Seq.append received c)
  with chunk and ()

(**
  [read_delivers] re-establishes the [received = committed ++ pending] invariant
  at the advanced history [received'] and the append-read buffer [b'].
**)
let lemma_read_delivers_preserves
  (received received' committed:TCP.bytes)
  (b b':BT.phys_buffer)
  : Lemma
      (requires
        BT.received_split received committed b /\
        BT.buffer_wf b /\
        read_delivers received received' b b')
      (ensures
        BT.buffer_wf b' /\ BT.received_split received' committed b')
= let chunk = FStar.IndefiniteDescription.indefinite_description_ghost
                TCP.bytes
                (fun chunk -> BT.chunk_fits b chunk /\
                              Seq.equal (BT.pending b') (Seq.append (BT.pending b) chunk) /\
                              Seq.equal received' (Seq.append received chunk)) in
  Seq.lemma_eq_elim received (Seq.append committed (BT.pending b));
  Seq.lemma_eq_elim (BT.pending b') (Seq.append (BT.pending b) chunk);
  Seq.lemma_eq_elim received' (Seq.append received chunk);
  Seq.append_assoc committed (BT.pending b) chunk

(**
  Process the exact current pending bytes and perform physical reads only after
  the processor returns a semantically justified [NeedMore].  [process] and
  [read] are explicit computational arguments so extraction can specialize
  them to direct calls while [ep] remains a proof-only dictionary.
**)
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
    drive_post
      ep
      e
      (Ghost.reveal st)
      outcome **
    pure (
      FStar.SizeT.v (drive_fuel_left outcome) <=
        FStar.SizeT.v fuel)
{
  let mut fuel_left = fuel;
  while (true)
    invariant live fuel_left
    invariant exists* received' committed' b'.
      ep.bse_owns
        e
        (Ghost.reveal st)
        received'
        committed'
        b' **
      pure (FStar.SizeT.v (Pulse.Lib.Reference.read fuel_left) <=
        FStar.SizeT.v fuel)
    decreases (FStar.SizeT.v (Pulse.Lib.Reference.read fuel_left))
  {
    let current_fuel = Pulse.Lib.Reference.read fuel_left;
    with received' committed' b'.
      assert (
        ep.bse_owns
          e
          (Ghost.reveal st)
          received'
          committed'
          b');
    if (current_fuel = 0sz) {
      fold
        (drive_post
          ep
          e
          (Ghost.reveal st)
          DriveExhausted);
      return DriveExhausted;
    };
    assert (pure (0 < FStar.SizeT.v current_fuel));
    let owns_wf = ep.bse_owns_wf;
    owns_wf
      e
      st
      (Ghost.hide received')
      (Ghost.hide committed')
      (Ghost.hide b');
    let processed =
      process
        e
        st
        (Ghost.hide received')
        (Ghost.hide committed')
        (Ghost.hide b');
    match processed {
      ProcessBufferFull r -> {
        unfold
          (process_post
            ep.bse_decide
            ep.bse_needs_more
            ep.bse_result_valid
            ep.bse_owns
            ep.bse_terminal
            ep.bse_buffer_full
            ep.bse_read_auth
            e
            (Ghost.reveal st)
            received'
            committed'
            b'
            (ProcessBufferFull r));
        assert (exists* st'.
          ep.bse_buffer_full e st' received' **
          pure (
            ep.bse_result_valid
              e
              (Ghost.reveal st)
              r
              st'));
        fold
          (drive_post
            ep
            e
            (Ghost.reveal st)
            (DriveBufferFull r current_fuel));
        return DriveBufferFull r current_fuel;
      }
      Processed r decision -> {
        unfold
          (process_post
            ep.bse_decide
            ep.bse_needs_more
            ep.bse_result_valid
            ep.bse_owns
            ep.bse_terminal
            ep.bse_buffer_full
            ep.bse_read_auth
            e
            (Ghost.reveal st)
            received'
            committed'
            b'
            (Processed r decision));
        match decision {
          NeedMore -> {
            with st' committed_after_process b_after_process.
              assert (
                ep.bse_read_auth
                  e st' received' committed_after_process b_after_process **
                pure (
                  ep.bse_needs_more
                    (Ghost.reveal st)
                    (BT.pending b') /\
                  decision == ep.bse_decide r /\
                  ep.bse_result_valid
                    e
                    (Ghost.reveal st)
                    r
                    st' /\
                  process_transition
                    decision
                    committed'
                    committed_after_process
                    b'
                    b_after_process /\
                  st' == Ghost.reveal st /\
                  BT.can_read b'));
            lemma_process_transition_needmore_stutter
              decision
              committed'
              committed_after_process
              b'
              b_after_process;
            rewrite
              (ep.bse_read_auth
                e
                st'
                received'
                committed_after_process
                b_after_process)
              as
              (ep.bse_read_auth
                e
                (Ghost.reveal st)
                received'
                committed'
                b');
            read
              e
              st
              (Ghost.hide received')
              (Ghost.hide committed')
              (Ghost.hide b');
            with received_after_read b_after_read.
              assert (
                ep.bse_owns
                  e
                  (Ghost.reveal st)
                  received_after_read
                  committed'
                  b_after_read **
                pure (
                  read_delivers
                    received'
                    received_after_read
                    b'
                    b_after_read));
            let next_fuel = FStar.SizeT.sub current_fuel 1sz;
            assert (pure (
              FStar.SizeT.v next_fuel < FStar.SizeT.v current_fuel /\
              FStar.SizeT.v next_fuel <= FStar.SizeT.v fuel));
            Pulse.Lib.Reference.write fuel_left next_fuel;
          }
          Progress consumed -> {
            assert (exists* st' committed_after_process b_after_process.
              ep.bse_owns
                e st' received' committed_after_process b_after_process **
              pure (
                ep.bse_result_valid
                  e
                  (Ghost.reveal st)
                  r
                  st'));
            assert (pure (ep.bse_decide r == Progress consumed));
            fold
              (drive_post
                ep
                e
                (Ghost.reveal st)
                (DriveProgress r consumed current_fuel));
            return DriveProgress r consumed current_fuel;
          }
          Yield consumed output -> {
            assert (exists* st' committed_after_process b_after_process.
              ep.bse_owns
                e st' received' committed_after_process b_after_process **
              pure (
                ep.bse_result_valid
                  e
                  (Ghost.reveal st)
                  r
                  st'));
            assert (pure (ep.bse_decide r == Yield consumed output));
            fold
              (drive_post
                ep
                e
                (Ghost.reveal st)
                (DriveYield r consumed output current_fuel));
            return DriveYield r consumed output current_fuel;
          }
          Reject error -> {
            assert (exists* st' received_after_process.
              ep.bse_terminal e st' received_after_process **
              pure (
                ep.bse_result_valid
                  e
                  (Ghost.reveal st)
                  r
                  st'));
            assert (pure (ep.bse_decide r == Reject error));
            fold
              (drive_post
                ep
                e
                (Ghost.reveal st)
                (DriveReject r error current_fuel));
            return DriveReject r error current_fuel;
          }
        }
      }
    }
  };
  unreachable ()
}
