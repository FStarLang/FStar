module Pulse.Lib.BufferedStream.Classifier

(**
  Layer 1 of [Pulse.Lib.BufferedStream]: the pure classifier model, for
  protocols that have a pure classifier (e.g. a length-prefixed framer).

  [Pulse.Lib.BufferedStream] re-exports this module (via [include]).

  A *stream processor* is a pure classifier

        sp_classify : state -> pending -> classification output error

  returning one of [NeedMore] / [Progress consumed] / [Yield consumed out] /
  [Reject err].  On top of it this module proves, as pure facts:

    * [needs_more] — the classifier says [NeedMore] for the *exact* current
      [state] and [pending].  IMPORTANT: [needs_more] is a duplicable *pure
      fact*, NOT a linear capability and NOT something that is "consumed".  It is
      the process-before-read *gate*: it records that a read is warranted.  The
      non-duplicable *right* to perform a read is the caller's stream ownership,
      modelled linearly in Layer 2 ([Pulse.Lib.BufferedStream]).

    * [NeedMore] is an exact stutter (no consumption, progress or output), and
      committing it is a buffer no-op ([lemma_needmore_stutter],
      [lemma_needmore_apply_noop]).

    * positive consumption is bounded by the pending length
      ([lemma_progress_positive], [lemma_consumption_bounded]).

    * conclusive decisions are prefix-stable under appended read-ahead
      ([lemma_conclusive_prefix_stable], [lemma_conclusive_prefix_stable2]) — the
      justification for processing the current pending before reading.

  The commit effects are threaded back to the [Pulse.Lib.BufferedTCP] buffer so the
  whole [received = committed ++ pending] transport invariant is preserved by
  every pure scheduler step ([lemma_step_commit_preserves]).

**)

module Seq = FStar.Seq
module SZ  = FStar.SizeT
module TCP = Pulse.Lib.TCP
module BT  = Pulse.Lib.BufferedTCP

type classification (output:Type0) (error:Type0) =
  | NeedMore : classification output error
  | Progress : consumed:SZ.t -> classification output error
  | Yield    : consumed:SZ.t -> out:output -> classification output error
  | Reject   : err:error -> classification output error

let consumed_of (#output #error:Type0) (d:classification output error) : SZ.t =
  match d with
  | NeedMore -> 0sz
  | Progress k -> k
  | Yield k _ -> k
  | Reject _ -> 0sz

(* ================================================================== *)
(*  Layer 1: pure classifier model                                    *)
(* ================================================================== *)

(* ------------------------------------------------------------------ *)
(*  Item (5): generic stream-processor classification                 *)
(* ------------------------------------------------------------------ *)

(** A decision is conclusive when it is not [NeedMore]. *)
let is_conclusive (#output #error:Type0) (d:classification output error) : bool =
  match d with
  | NeedMore -> false
  | _ -> true

(** A decision makes forward progress (consumes and advances). *)
let makes_progress (#output #error:Type0) (d:classification output error) : bool =
  match d with
  | Progress _ -> true
  | Yield _ _ -> true
  | _ -> false

(** A decision emits an application output. *)
let produces_output (#output #error:Type0) (d:classification output error) : bool =
  match d with
  | Yield _ _ -> true
  | _ -> false

(* ------------------------------------------------------------------ *)
(*  The stream-processor classifier laws                              *)
(* ------------------------------------------------------------------ *)

(**
  Positive consumption is bounded: a decision never consumes more than the
  pending bytes, and a progress-making decision consumes at least one byte
  (so it cannot masquerade as a stutter).
**)
let consumption_law
  (#state #output #error:Type0)
  (classify:state -> TCP.bytes -> classification output error)
  (st:state)
  (pending:TCP.bytes)
  : prop =
  SZ.v (consumed_of (classify st pending)) <= Seq.length pending /\
  (makes_progress (classify st pending) ==>
    SZ.v (consumed_of (classify st pending)) > 0)

(**
  Conclusive decisions are prefix-stable: reading ahead (appending [extra]
  bytes) does not change a conclusive decision.
**)
let prefix_stable_law
  (#state #output #error:Type0)
  (classify:state -> TCP.bytes -> classification output error)
  (st:state)
  (pending:TCP.bytes)
  (extra:TCP.bytes)
  : prop =
  is_conclusive (classify st pending) ==>
    classify st (Seq.append pending extra) == classify st pending

noextract
class stream_processor (state:Type0) (output:Type0) (error:Type0) =
{
  sp_classify:
    state -> TCP.bytes -> classification output error;

  sp_consumption:
    st:state ->
    pending:TCP.bytes ->
      Lemma (consumption_law sp_classify st pending);

  sp_prefix_stable:
    st:state ->
    pending:TCP.bytes ->
    extra:TCP.bytes ->
      Lemma
        (requires is_conclusive (sp_classify st pending))
        (ensures
          sp_classify st (Seq.append pending extra) == sp_classify st pending);
}

(* ------------------------------------------------------------------ *)
(*  Both classifier laws hold, at the predicate level, for any instance *)
(* ------------------------------------------------------------------ *)

(** Every instance satisfies the reusable [consumption_law] predicate. *)
let lemma_instance_consumption_law
  (#state #output #error:Type0)
  (sp:stream_processor state output error)
  (st:state)
  (pending:TCP.bytes)
  : Lemma (ensures consumption_law sp.sp_classify st pending)
= sp.sp_consumption st pending

(** Every instance satisfies the reusable [prefix_stable_law] predicate. *)
let lemma_instance_prefix_stable_law
  (#state #output #error:Type0)
  (sp:stream_processor state output error)
  (st:state)
  (pending extra:TCP.bytes)
  : Lemma (ensures prefix_stable_law sp.sp_classify st pending extra)
= if is_conclusive (sp.sp_classify st pending)
  then sp.sp_prefix_stable st pending extra
  else ()

(* ------------------------------------------------------------------ *)
(*  Bounded consumption                                               *)
(* ------------------------------------------------------------------ *)

let lemma_consumption_bounded
  (#state #output #error:Type0)
  (sp:stream_processor state output error)
  (st:state)
  (pending:TCP.bytes)
  : Lemma
      (ensures
        SZ.v (consumed_of (sp.sp_classify st pending)) <= Seq.length pending)
= sp.sp_consumption st pending

let lemma_progress_positive
  (#state #output #error:Type0)
  (sp:stream_processor state output error)
  (st:state)
  (pending:TCP.bytes)
  : Lemma
      (requires makes_progress (sp.sp_classify st pending))
      (ensures
        0 < SZ.v (consumed_of (sp.sp_classify st pending)) /\
        SZ.v (consumed_of (sp.sp_classify st pending)) <= Seq.length pending)
= sp.sp_consumption st pending

(* ------------------------------------------------------------------ *)
(*  Item (6a): the process-before-read gate  [needs_more]             *)
(* ------------------------------------------------------------------ *)

(**
  [needs_more sp st pending] holds precisely when the classifier says [NeedMore]
  for the *exact* [st] and [pending].  It is a duplicable PURE fact — the
  process-before-read gate — NOT a linear capability and NOT "consumed" by
  reading.  The non-duplicable right to read is the caller's stream ownership
  (Layer 2, [bse_owns] / [bse_read_auth]).
**)
let needs_more
  (#state #output #error:Type0)
  (sp:stream_processor state output error)
  (st:state)
  (pending:TCP.bytes)
  : prop =
  sp.sp_classify st pending == NeedMore

let lemma_needs_more_iff
  (#state #output #error:Type0)
  (sp:stream_processor state output error)
  (st:state)
  (pending:TCP.bytes)
  : Lemma
      (ensures (needs_more sp st pending <==> sp.sp_classify st pending == NeedMore))
= ()

(** [needs_more] and a conclusive decision are mutually exclusive. *)
let lemma_needmore_not_conclusive
  (#state #output #error:Type0)
  (sp:stream_processor state output error)
  (st:state)
  (pending:TCP.bytes)
  : Lemma
      (requires needs_more sp st pending)
      (ensures ~(is_conclusive (sp.sp_classify st pending)))
= ()

let lemma_conclusive_not_needs_more
  (#state #output #error:Type0)
  (sp:stream_processor state output error)
  (st:state)
  (pending:TCP.bytes)
  : Lemma
      (requires is_conclusive (sp.sp_classify st pending))
      (ensures ~(needs_more sp st pending))
= ()

(**
  The gate is *state specific*: [needs_more] at [st] cannot coexist with a
  conclusive decision at a state [st'] on the same pending — so [st =!= st'].
**)
let lemma_needs_more_state_specific
  (#state #output #error:Type0)
  (sp:stream_processor state output error)
  (st st':state)
  (pending:TCP.bytes)
  : Lemma
      (requires needs_more sp st pending /\ is_conclusive (sp.sp_classify st' pending))
      (ensures ~(st == st'))
= ()

(**
  The gate is *pending specific*: [needs_more] at [pending] cannot coexist with a
  conclusive decision at a different [pending'] in the same state — so
  [pending =!= pending'].  After the pending bytes change (e.g. by a read), the
  gate must be re-derived.
**)
let lemma_needs_more_pending_specific
  (#state #output #error:Type0)
  (sp:stream_processor state output error)
  (st:state)
  (pending pending':TCP.bytes)
  : Lemma
      (requires needs_more sp st pending /\ is_conclusive (sp.sp_classify st pending'))
      (ensures ~(pending == pending'))
= ()

(* ------------------------------------------------------------------ *)
(*  Item (6b): NeedMore is a stutter / no output                      *)
(* ------------------------------------------------------------------ *)

let lemma_needmore_stutter
  (#state #output #error:Type0)
  (sp:stream_processor state output error)
  (st:state)
  (pending:TCP.bytes)
  : Lemma
      (requires needs_more sp st pending)
      (ensures
        consumed_of (sp.sp_classify st pending) == 0sz /\
        ~(makes_progress (sp.sp_classify st pending)) /\
        ~(produces_output (sp.sp_classify st pending)))
= ()

(* ------------------------------------------------------------------ *)
(*  Item (6c): conclusive decisions are prefix-stable                 *)
(* ------------------------------------------------------------------ *)

(** One read-ahead: a conclusive decision is unchanged by appended bytes. *)
let lemma_conclusive_prefix_stable
  (#state #output #error:Type0)
  (sp:stream_processor state output error)
  (st:state)
  (pending extra:TCP.bytes)
  : Lemma
      (requires is_conclusive (sp.sp_classify st pending))
      (ensures sp.sp_classify st (Seq.append pending extra) == sp.sp_classify st pending)
= sp.sp_prefix_stable st pending extra

(** Two successive read-aheads: still the same conclusive decision. *)
let lemma_conclusive_prefix_stable2
  (#state #output #error:Type0)
  (sp:stream_processor state output error)
  (st:state)
  (pending extra1 extra2:TCP.bytes)
  : Lemma
      (requires is_conclusive (sp.sp_classify st pending))
      (ensures
        sp.sp_classify st (Seq.append (Seq.append pending extra1) extra2)
        == sp.sp_classify st pending)
= sp.sp_prefix_stable st pending extra1;
  sp.sp_prefix_stable st (Seq.append pending extra1) extra2

(* ------------------------------------------------------------------ *)
(*  Item (6): explicit process-before-read phases                     *)
(* ------------------------------------------------------------------ *)

(**
  The two scheduling phases of the process-before-read discipline.  In the
  [Reading] phase the scheduler must read more bytes; in the [Processing] phase
  it must act on a conclusive decision.  The phase is *computed from* the current
  state and pending bytes, so "which phase" is dictated by the classifier.
**)
type phase =
  | Reading
  | Processing

let current_phase
  (#state #output #error:Type0)
  (sp:stream_processor state output error)
  (st:state)
  (pending:TCP.bytes)
  : phase =
  if is_conclusive (sp.sp_classify st pending) then Processing else Reading

(** The [Reading] phase is *exactly* where the gate [needs_more] holds. *)
let lemma_phase_reading_iff_needs_more
  (#state #output #error:Type0)
  (sp:stream_processor state output error)
  (st:state)
  (pending:TCP.bytes)
  : Lemma
      (ensures (current_phase sp st pending == Reading <==> needs_more sp st pending))
= ()

(** The [Processing] phase is *exactly* where the decision is conclusive. *)
let lemma_phase_processing_iff_conclusive
  (#state #output #error:Type0)
  (sp:stream_processor state output error)
  (st:state)
  (pending:TCP.bytes)
  : Lemma
      (ensures
        (current_phase sp st pending == Processing <==>
         is_conclusive (sp.sp_classify st pending)))
= ()

(**
  The process-before-read *dichotomy*: in any configuration the scheduler is in
  exactly one of two phases — a read phase (the gate holds and the decision is
  not yet conclusive) or a process phase (the decision is conclusive and the gate
  does not hold).  This licenses "process first, read only on [NeedMore]".
**)
let lemma_process_read_dichotomy
  (#state #output #error:Type0)
  (sp:stream_processor state output error)
  (st:state)
  (pending:TCP.bytes)
  : Lemma
      (ensures
        (needs_more sp st pending /\ ~(is_conclusive (sp.sp_classify st pending))) \/
        (is_conclusive (sp.sp_classify st pending) /\ ~(needs_more sp st pending)))
= ()

(* ------------------------------------------------------------------ *)
(*  Pure scheduler step effects on the buffered-TCP state             *)
(* ------------------------------------------------------------------ *)

(**
  The transport-and-buffer invariant a concrete wrapper maintains: the buffer is
  well-formed (fixed capacity, dense pending prefix) and the received stream is
  the committed prefix followed by the buffer's pending region.
**)
let stream_invariant
  (received committed:TCP.bytes)
  (b:BT.phys_buffer)
  : prop =
  BT.buffer_wf b /\ BT.received_split received committed b

(** The classifier's consumption is always a valid commit count for the buffer. *)
let lemma_commit_count_ok
  (#state #output #error:Type0)
  (sp:stream_processor state output error)
  (st:state)
  (b:BT.phys_buffer)
  : Lemma
      (requires BT.buffer_wf b)
      (ensures
        SZ.v (consumed_of (sp.sp_classify st (BT.pending b))) <=
          Seq.length (BT.pending b))
= sp.sp_consumption st (BT.pending b);
  BT.lemma_pending_length b

(**
  Commit a scheduler decision to the buffer: the committed prefix grows by the
  consumed bytes and the buffer is compacted.
**)
let step_commit
  (#state #output #error:Type0)
  (sp:stream_processor state output error)
  (st:state)
  (committed:TCP.bytes)
  (b:BT.phys_buffer)
  : (TCP.bytes & BT.phys_buffer) =
  let k = consumed_of (sp.sp_classify st (BT.pending b)) in
  (BT.committed_after committed b (SZ.v k), BT.compact b (SZ.v k))

(**
  Core scheduler theorem: committing *any* classifier decision preserves the
  whole [received = committed ++ pending] invariant and the fixed-capacity
  buffer well-formedness.
**)
let lemma_step_commit_preserves
  (#state #output #error:Type0)
  (sp:stream_processor state output error)
  (st:state)
  (received committed:TCP.bytes)
  (b:BT.phys_buffer)
  : Lemma
      (requires stream_invariant received committed b)
      (ensures
        (let (committed', b') = step_commit sp st committed b in
         stream_invariant received committed' b'))
= lemma_commit_count_ok sp st b;
  let k = consumed_of (sp.sp_classify st (BT.pending b)) in
  BT.lemma_commit_preserves_full received committed b (SZ.v k);
  BT.lemma_compact_wf b (SZ.v k)

(** The committed stream only ever grows when a decision is committed. *)
let lemma_step_commit_extends
  (#state #output #error:Type0)
  (sp:stream_processor state output error)
  (st:state)
  (committed:TCP.bytes)
  (b:BT.phys_buffer)
  : Lemma
      (ensures
        (let (committed', _) = step_commit sp st committed b in
         TCP.bytes_extends committed committed'))
= let k = consumed_of (sp.sp_classify st (BT.pending b)) in
  BT.lemma_committed_after_extends committed b (SZ.v k)

(**
  Committing a [NeedMore] decision is a buffer no-op: the committed prefix and
  the pending region are unchanged — a genuine stutter that only a read can
  break.
**)
let lemma_needmore_apply_noop
  (#state #output #error:Type0)
  (sp:stream_processor state output error)
  (st:state)
  (committed:TCP.bytes)
  (b:BT.phys_buffer)
  : Lemma
      (requires needs_more sp st (BT.pending b) /\ BT.buffer_wf b)
      (ensures
        (let (committed', b') = step_commit sp st committed b in
         Seq.equal committed' committed /\
         Seq.equal (BT.pending b') (BT.pending b)))
= BT.lemma_compact_pending b 0;
  Seq.append_empty_r committed;
  Seq.lemma_eq_intro (BT.committed_after committed b 0) committed

(* ------------------------------------------------------------------ *)
(*  Item (6d): a warranted read (a PURE fact, not a capability)       *)
(* ------------------------------------------------------------------ *)

(**
  A PURE specification of a warranted read: the classifier needs more input at
  the exact current [st] and pending [BT.pending b], the delivered [chunk] fits
  the free capacity, and [b'] is the append-read of [chunk] into [b].

  This is a *pure fact*, NOT a linear capability and NOT "consumed" by reading.
  It records that a read is warranted; the non-duplicable *right* to perform it
  is the endpoint's exclusive [bse_read_auth] state in the Layer-2 relational
  adapter [buffered_stream_endpoint].
**)
let read_warranted
  (#state #output #error:Type0)
  (sp:stream_processor state output error)
  (st:state)
  (b b':BT.phys_buffer)
  (chunk:TCP.bytes)
  : prop =
  needs_more sp st (BT.pending b) /\
  BT.chunk_fits b chunk /\
  b' == BT.append_read b chunk

(** The buffer effect of a warranted read: pending grows by [chunk]. *)
let lemma_read_warranted_effect
  (#state #output #error:Type0)
  (sp:stream_processor state output error)
  (st:state)
  (b b':BT.phys_buffer)
  (chunk:TCP.bytes)
  : Lemma
      (requires read_warranted sp st b b' chunk /\ BT.buffer_wf b)
      (ensures
        BT.buffer_wf b' /\
        BT.capacity b' == BT.capacity b /\
        Seq.equal (BT.pending b') (Seq.append (BT.pending b) chunk))
= BT.lemma_append_read_wf b chunk;
  BT.lemma_append_read_capacity b chunk;
  BT.lemma_append_read_pending b chunk

(**
  Process-before-read: a read is warranted only in the [Reading] phase, never in
  the [Processing] phase.  So the scheduler always processes a conclusive
  decision before it is allowed to read again.
**)
let lemma_read_only_in_reading_phase
  (#state #output #error:Type0)
  (sp:stream_processor state output error)
  (st:state)
  (b b':BT.phys_buffer)
  (chunk:TCP.bytes)
  : Lemma
      (requires read_warranted sp st b b' chunk)
      (ensures current_phase sp st (BT.pending b) == Reading)
= ()

(**
  Core scheduler theorem for reads: a warranted read preserves the invariant,
  extending the received stream by exactly the delivered chunk.
**)
let lemma_step_read_preserves
  (#state #output #error:Type0)
  (sp:stream_processor state output error)
  (st:state)
  (received committed:TCP.bytes)
  (b b':BT.phys_buffer)
  (chunk:TCP.bytes)
  : Lemma
      (requires read_warranted sp st b b' chunk /\ stream_invariant received committed b)
      (ensures stream_invariant (Seq.append received chunk) committed b')
= BT.lemma_append_read_extends_received received committed b chunk;
  BT.lemma_append_read_wf b chunk

(**
  After a read the pending region is [BT.pending b ++ chunk]; whether a further
  read is warranted depends on a *fresh* classification of that new pending.  The
  scheduler therefore re-enters the process-before-read dichotomy at [b'].
**)
let lemma_after_read_dichotomy
  (#state #output #error:Type0)
  (sp:stream_processor state output error)
  (st:state)
  (b':BT.phys_buffer)
  : Lemma
      (ensures
        (needs_more sp st (BT.pending b') /\ ~(is_conclusive (sp.sp_classify st (BT.pending b')))) \/
        (is_conclusive (sp.sp_classify st (BT.pending b')) /\ ~(needs_more sp st (BT.pending b'))))
= ()

(**
  If the classifier concludes on the current pending, then it would have reached
  the *same* decision after any read-ahead.  Hence it is always sound to process
  the current pending *before* reading: reading first can never turn a conclusive
  decision into a different one.
**)
let lemma_process_before_read_sound
  (#state #output #error:Type0)
  (sp:stream_processor state output error)
  (st:state)
  (b b':BT.phys_buffer)
  (chunk:TCP.bytes)
  : Lemma
      (requires
        is_conclusive (sp.sp_classify st (BT.pending b)) /\
        BT.buffer_wf b /\
        BT.chunk_fits b chunk /\
        b' == BT.append_read b chunk)
      (ensures sp.sp_classify st (BT.pending b') == sp.sp_classify st (BT.pending b))
= BT.lemma_append_read_pending b chunk;
  sp.sp_prefix_stable st (BT.pending b) chunk;
  Seq.lemma_eq_elim (BT.pending b') (Seq.append (BT.pending b) chunk)
