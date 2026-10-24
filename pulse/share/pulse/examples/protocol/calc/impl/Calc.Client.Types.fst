module Calc.Client.Types

#lang-pulse

(**
  Concrete client state for the calculator client.

  The client is implemented as a *predicted server* (a full `server_state` that
  simulates what the peer server does, so every verified server handler can be
  reused for response prediction) plus a buffer holding the wire bytes of the
  currently-outstanding request.

  `client_exactly c st` ties the concrete state `c` to the abstract client
  state `st` (see `Calc.Client.Log`): the predicted server owns exactly the
  completed round-trips, and, when a request is pending, the `pending` buffer
  holds its wire bytes.
**)

module U8 = FStar.UInt8
module Seq = FStar.Seq

open Pulse.Lib.Pervasives
module Vec = Pulse.Lib.Vec

open Calc.Log
open Calc.Impl.Types
open Calc.Client.Log

(** Concrete client: a simulated server + the pending request's wire bytes. **)
noeq
type client_state = {
  predicted: server_state;   // simulates the peer server to predict responses
  pending: Vec.vec U8.t;      // wire bytes of the outstanding request (5 bytes)
}

(** Knowledge that the client is exactly at abstract state `st`. **)
let client_exactly (c: client_state) (st: client_state_abs) : slprop =
  exists* (pend: Seq.seq U8.t).
    server_exactly c.predicted st.completed **
    Vec.pts_to c.pending pend **
    pure (
      Seq.length pend == 5 /\
      (match st.pending with
       | None -> True
       | Some b -> pend == b)
    )
