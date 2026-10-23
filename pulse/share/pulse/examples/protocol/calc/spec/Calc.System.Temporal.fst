module Calc.System.Temporal

(**
  Temporal-logic theorems about the combined calculator client–server system.

  Using the generic path-based operators of `Pulse.Lib.Protocol.Temporal` over the transition
  system of `Calc.System`, we prove:

    1. Flagship safety (quiescent agreement):
         AG (quiescent  ==>  client_stack = server_stack)
       "whenever no message is in flight, the client and server stacks agree".
       (The naive `AG (client_stack = server_stack)` is false mid-delivery.)

    2. A `next` (X) property exercising the operator vocabulary:
       from an idle/quiescent state the *next* state always has a request in
       flight (the only enabled move is to issue a request).

    3. Liveness under fairness:
         AG (message in flight  ==>  F quiescent)
       "every outstanding request is eventually completed", assuming a fair run
       (no message stays in flight forever).
**)

module T = Pulse.Lib.Protocol.Temporal
module R = FStar.ReflexiveTransitiveClosure
module MP = Pulse.Lib.Protocol.MachineProduct
module SM = Pulse.Lib.Protocol.StateMachine
module CalcP = Calc.Protocol

open Calc.Spec
open Calc.Log
open Calc.Client.Log
open Calc.System

(** ─────────────────────────────────────────────────────────────────────────
    1. Flagship: AG (quiescent ==> client_stack = server_stack)
    ───────────────────────────────────────────────────────────────────────── **)

let stacks_agree_when_quiescent (s:system_state) : prop =
  quiescent s ==> client_stack s == server_stack s

(** The invariant entails the flagship state-predicate. **)
val lemma_inv_implies_agreement (s:system_state)
  : Lemma (requires system_inv s)
          (ensures stacks_agree_when_quiescent s)
let lemma_inv_implies_agreement s =
  match s.channel with
  | MP.Quiet ->
    // system_inv gives  s.server == s.client.completed, hence equal stacks.
    ()
  | _ -> ()  // not quiescent: implication holds vacuously

(**
  Flagship theorem: on *every* run of the system from the initial state, it is
  *always* the case that if the system is quiescent then the two stacks agree.
**)
val lemma_flagship_quiescent_agreement (_:unit)
  : Lemma (T.ag sys_step stacks_agree_when_quiescent initial_system)
let lemma_flagship_quiescent_agreement () =
  introduce
    forall (s':system_state).
      T.reachable sys_step initial_system s' ==> stacks_agree_when_quiescent s'
  with begin
    introduce
      T.reachable sys_step initial_system s' ==> stacks_agree_when_quiescent s'
    with begin
      lemma_reachable_inv s';
      lemma_inv_implies_agreement s'
    end
  end;
  T.lemma_ag_of_invariant sys_step stacks_agree_when_quiescent initial_system

(** ─────────────────────────────────────────────────────────────────────────
    2. A next-step (X) property.
    ───────────────────────────────────────────────────────────────────────── **)

let request_in_flight (s:system_state) : prop = MP.ToServer? s.channel

(**
  From an idle, quiescent state the only enabled transition is to issue a
  request, so on any run the *next* state has a request in flight: `X (MP.ToServer)`.
**)
val lemma_x_next_is_request (p:T.path system_state)
  : Lemma
      (requires
        T.is_run sys_step p /\
        MP.Quiet? (p 0).channel /\
        None? (p 0).client.pending)
      (ensures T.holds_X request_in_flight p)
let lemma_x_next_is_request p =
  assert (sys_step (p 0) (p 1));  // from is_run at index 0
  // At a quiet channel the only enabled derived family is the client's send
  // (`request_response_moves` disables the other three), and a client send
  // leaves the channel holding a request directed at the server.
  MP.lemma_step_channel_cases calc_machine_iface (p 0) (p 1);
  assert (MP.mp_client_send calc_machine_iface (p 0) (p 1));
  eliminate exists (local:calc_client_local_event)
                   (c':client_state_abs)
                   (out:SM.step_output CalcP.calc_frame unit)
                   (q:calc_payload).
    MP.mp_client_send_body calc_machine_iface (p 0) (p 1) local c' out q
  with ()

(** ─────────────────────────────────────────────────────────────────────────
    3. Liveness under fairness: AG (in flight ==> F quiescent)
    ───────────────────────────────────────────────────────────────────────── **)

let in_flight (s:system_state) : prop = ~(MP.Quiet? s.channel)

(** Rank of the channel: quiescent = 0, response in flight = 1, request = 2. **)
let chan_rank (c:MP.chan calc_payload) : nat =
  match c with
  | MP.Quiet      -> 0
  | MP.ToClient _ -> 1
  | MP.ToServer _ -> 2

(**
  Fairness: no message stays in flight forever. From any state that is not
  quiescent, the channel's rank strictly decreases at some strictly later
  position (a real delivery step is eventually taken rather than stuttering).
**)
let fair (p:T.path system_state) : prop =
  forall (i:nat).
    ~(MP.Quiet? (p i).channel) ==>
    (exists (j:nat). j > i /\ chan_rank (p j).channel < chan_rank (p i).channel)

(**
  On a fair run, from any position the system eventually becomes quiescent.
  Proved by well-founded recursion on the channel rank: fairness supplies a
  strictly-lower-rank future position, and we recurse there.
**)
val lemma_eventually_quiescent (p:T.path system_state) (i:nat)
  : Lemma
      (requires fair p)
      (ensures exists (k:nat). k >= i /\ MP.Quiet? (p k).channel)
      (decreases (chan_rank (p i).channel))
let rec lemma_eventually_quiescent p i =
  if MP.Quiet? (p i).channel
  then ()  // witness k = i
  else begin
    // fairness at i gives a strictly-lower-rank position j > i
    eliminate
      exists (j:nat). j > i /\ chan_rank (p j).channel < chan_rank (p i).channel
    with begin
      lemma_eventually_quiescent p j;  // decreases: chan_rank (p j) < chan_rank (p i)
      // IH: exists k >= j. Quiet (p k); since j > i, also k >= i.
      ()
    end
  end

(**
  Liveness theorem: on any fair run, it is always the case that if a message is
  in flight then the system eventually becomes quiescent again — i.e. every
  outstanding request is eventually completed.  `AG (in_flight ==> F quiescent)`.
**)
val lemma_liveness_response_delivered (p:T.path system_state)
  : Lemma
      (requires fair p)
      (ensures
        (forall (i:nat).
          in_flight (p i) ==> T.holds_F quiescent (T.shift p i)))
let lemma_liveness_response_delivered p =
  introduce
    forall (i:nat). in_flight (p i) ==> T.holds_F quiescent (T.shift p i)
  with begin
    introduce in_flight (p i) ==> T.holds_F quiescent (T.shift p i)
    with begin
      lemma_eventually_quiescent p i;
      // exists k >= i. Quiet (p k); set m = k - i so (shift p i) m = p k.
      eliminate exists (k:nat). k >= i /\ MP.Quiet? (p k).channel
      with begin
        let m : nat = k - i in
        assert (T.shift p i m == p k);
        assert (quiescent (T.shift p i m))
      end
    end
  end
