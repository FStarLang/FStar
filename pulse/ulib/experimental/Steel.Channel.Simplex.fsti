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

module Steel.Channel.Simplex
open Steel.Channel.Protocol
open Steel.Memory
open Steel.Effect

/// This library provides a model of unidirectional, protocol-indexed channels.
/// One party is allowed to send messages on the channel, while the other is allowed
/// to receive messages on the same channel.
/// Protocols are specified using the structure in Steel.Channel.Protocol


/// Msg int (fun x -> Msg (y:int { y > x }) (fun _ -> Ret unit))
///
/// DoWhile (Msg int (fun x -> Msg (y:int { y > x }) (fun _ -> Ret bool)))
let prot : Type u#1 = protocol unit

/// The abstract type of indexed channels
val chan (p:prot) : Type0

/// The separation logic predicate stating that a party has permission to send
/// messages on channel [c] which follows protocol [p], and that the protocol
/// is at a stage where [next_action] remains to be executed
val sender (#p:prot) (c:chan p) (next_action:prot) : vprop

/// The separation logic predicate stating that a party has permission to receive
/// messages on channel [c] which follows protocol [p], and that the protocol
/// is at a stage where [next_action] remains to be executed
val receiver (#p:prot) (c:chan p) (next_action:prot) : vprop

/// Creating a new channel for a given protocol [p].
/// This returns permissions to use channel [c] for protocol [p] to respectively send
/// and receive messages
val new_chan (p:prot)
  : SteelT (chan p) emp (fun c -> sender c p `star` receiver c p)

/// Sending a message [x] on channel [c], as long as it is valid with respect to
/// the current state of the protocol [next]. The protocol is then advanced one step.
val send (#p:prot) (c:chan p) (#next:prot{more next}) (x:msg_t next)
  : SteelT unit (sender c next) (fun _ -> sender c (step next x))

/// Receives a message on channel [c], which is ensured to be valid with respect
/// to the current state of the protocol [next]. The protocol is then advanced one step
val recv (#p:prot) (#next:prot{more next}) (c:chan p)
  : SteelT (msg_t next) (receiver c next) (fun x -> receiver c (step next x))

/// A pure predicate stating that trace [t] contains messages exchanged on channel [c],
/// which follows protocol [p]
val history (#p:prot) (c:chan p) (t:partial_trace_of p) : prop

/// Extracting the current trace of messages exchanged on channel [cc]
val trace (#q:prot) (cc:chan q)
  : Steel (partial_trace_of q) emp (fun _ -> emp)
          (requires fun _ -> True)
          (ensures fun _ tr _ -> history cc tr)

/// If [previous] is a trace of messages that were previously exchanged on channel [c],
/// and if the protocol on this channel has since advanced to stage [next], then
/// we can extend [previous] with the newly exchanged messages
val extend_trace (#p:prot) (#next:prot) (c:chan p) (previous:partial_trace_of p)
  : Steel (extension_of previous)
          (receiver c next)
          (fun t -> receiver c next)
          (requires fun _ -> history c previous)
          (ensures fun _ t _ -> until t == next /\ history c t)
