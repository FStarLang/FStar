(*
   Copyright 2020 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)

module Steel.Channel.Duplex
open Steel.Channel.Protocol
open Steel.Memory
open Steel.Effect

/// This library provides a model of two-party session types in Steel.
/// Protocols are specified using the structure in Steel.Channel.Protocol
/// Channels are indexed by a given protocols, and ensure that any message exchanged
/// on the channel respect the protocol.
/// An implementation of this model is currently available in Duplex.PCM.fst

/// Msg int (fun x -> Msg (y:int { y > x }) (fun _ -> Ret unit))
///
/// DoWhile (Msg int (fun x -> Msg (y:int { y > x }) (fun _ -> Ret bool)))
let prot : Type u#1 = protocol unit

/// The abstract type of indexed channels
val chan (p:prot) : Type0

/// The endpoint separation logic predicate stating that for a given channel [c],
/// indexed by protocol [p], we are currently at the stage where [next_action]
/// remains to be executed on this channel.
val endpoint (#p:prot) (c:chan p) (next_action:prot) : vprop

/// Creating a new channel for a given protocol [p].
/// This returns permissions for the two parties to use channel [c] for protocol [p].
/// The second party receives permission for the dual protocol, where Sent and Received
/// messages are swapped
val new_chan (p:prot)
  : SteelT (chan p) emp (fun c -> endpoint c p `star` endpoint c (dual p))

/// Sending a message [x] on channel [c], as long as the message is valid with respect to
/// the current state of the protocol [next]. The protocol is then advanced one step
val send (#p:prot)
         (c:chan p)
         (#next:prot{more next /\ tag_of next = Send})
         (x:msg_t next)
  : SteelT unit
           (endpoint c next)
           (fun _ -> endpoint c (step next x))

/// Receiving a message on channel [c], which is ensured to be valid with respect to
/// the current state of the protocol [next]. The protocol is then advanced one step
val recv (#p:prot)
         (#next:prot{more next /\ tag_of next = Recv})
         (c:chan p)
  : SteelT (msg_t next)
           (endpoint c next)
           (fun x -> endpoint c (step next x))

/// A separation logic predicate stating that trace [t] is a valid partial trace for protocol [p]
val history (#p:prot) (c:chan p) (t:partial_trace_of p) : vprop

/// history is a pure predicate, which is duplicable
val history_duplicable (#p:prot) (c:chan p) (t:partial_trace_of p)
  : SteelT unit (history c t) (fun _ -> history c t `star` history c t)

/// Returning the current trace of messages exchanged on channel [cc], which
/// is a valid trace with respect to the protocol [q]
val trace (#q:prot) (cc:chan q)
  : SteelT (partial_trace_of q) emp (fun tr -> history cc tr)

/// If [previous] is a trace of messages previously exchanged on channel [c],
/// and if the protocol on channel [c] has since advanced to state [next], then
/// we can extend the trace [previous] with the messages exchanged since
val extend_trace (#p:prot) (#next:prot) (c:chan p) (previous:partial_trace_of p)
  : SteelT (extension_of previous)
           (endpoint c next `star` history c previous)
           (fun t -> endpoint c next `star` history c t `star` pure (until t == next))
