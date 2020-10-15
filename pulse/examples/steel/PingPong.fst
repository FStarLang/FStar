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

module PingPong
open Steel.Effect
open Steel.Memory
open Steel.Channel.Protocol
module Duplex = Steel.Channel.Duplex
module Protocol = Steel.Channel.Protocol
//open Steel.SteelT.Basics

(** Specification and implementation of a pingpong protocol *)

/// Specification of a pingpong protocol.
/// The protocol consists of two messages.
/// A client first sends an integer on a channel.
/// It then receives an integer that is ensured to be strictly greater than the one she sent
/// The protocol then terminates by returning unit (done)
let pingpong : Duplex.prot =
  x <-- Protocol.send int;
  y <-- Protocol.recv (y:int{y > x});
  Protocol.done

/// An implementation of the pingpong protocol specified above.
/// The client takes as an argument a channel that satisfies the pingpong protocol
/// Additionally, it requires the separation logic assertion `endpoint c pingpong`
/// that indicates ownership of an endpoint for channel c, and that the protocol did not
/// start yet.
/// After execution, the postcondition specifies ownership of an endpoint for channel c,
/// but no action in the protocol remains.
let client (c:Duplex.chan pingpong)
  : SteelT unit
           (Duplex.endpoint c pingpong)
           (fun _ -> Duplex.endpoint c Protocol.done)
  = // In this implementation, the client first sends the (arbitrarily chosen) integer 17
    Duplex.send c 17;
    let y = Duplex.recv c in
    // The protocol specifies that the integer received is greater than the one sent.
    // This fact is available in the context and can be asserted.
    assert (y > 17);
    // To end the protocol, we return unit
    ()


/// An implementation of the server side of the protocol.
/// Similarly to the client side, it takes as argument a channel that corresponds to the pingpong protocol.
/// It initially owns the separation logic assertion `endpoint c (P.dual pingpong)`,
/// where `dual pingpong` is the pingpong protocol where receives and sends are flipped.
/// After execution, the postcondition `endpoint c P.done` again specifies that the protocol
/// is done on channel c
let server (c:Duplex.chan pingpong)
  : SteelT unit
           (Duplex.endpoint c (Protocol.dual pingpong))
           (fun _ -> Duplex.endpoint c Protocol.done)
  = let y = Duplex.recv c in
    // The dual protocol specifies that an integer is received, and that a greater integer
    // must be sent. We arbitrarily choose y + 42
    Duplex.send c (y + 42);
    ()

/// A wrong implementation of the server side of the protocol.
/// If the `expect_failure` attribute is commented out, this function does not typecheck
[@expect_failure]
let failed_server (c:Duplex.chan pingpong)
  : SteelT unit
           (Duplex.endpoint c (Protocol.dual pingpong))
           (fun _ -> Duplex.endpoint c Protocol.done)
  = let y = Duplex.recv c in
    // This send does not satisfy the protocol, as the integer should be greater than y
    // The error message points to the value sent not satisfying the protocol
    Duplex.send c (y - 42);
    ()


/// Initialization of both the client and the server side of the pingpong protocol.
/// Both sides are executed in parallel using the `par` combinator
let client_server (_:unit)
  : SteelT unit emp (fun _ -> emp)
  = // Creates a new channel `c` for the pingpong protocol.
    // After creation, an endpoint for the pingpong protocol and
    // for the dual protocol are available
    let c = Duplex.new_chan pingpong in
    // The separation logic assertion `endpoint c pingpong <*> endpoint c (dual pingpong)`
    // is in the context. We can execute both the clients in the server in parallel,
    // as they both operate on separated resources
    let _ = par (fun _ -> client c) (fun _ -> server c) in
    // Our separation logic is affine, we can drop the endpoints from the context
    // to make them unavailable from outside client_server
    drop (Duplex.endpoint c Protocol.done `star` Duplex.endpoint c Protocol.done)

module T = Steel.Primitive.ForkJoin

(** Execution of a multitude of client_server instances in parallel *)

let rec join_all (threads:list (T.thread emp))
  : SteelT unit emp (fun _ -> emp)
  = let open FStar.List.Tot.Base in
    if isEmpty threads then (noop #emp (); ()) else
      (let Cons hd tl = threads in T.join hd; join_all tl)

/// We leverage an existing fork/join library to execute n instances of client_server in parallel
/// This function accumulates all created threads in its second argument.
/// Once it spawned n instances (when n = 0), it joins all of them using the join_all helper
/// defined above, waiting for all threads to terminate before finally returning unit
/// If it still needs to spawn instances (n > 0), it executes a new instance of client_server
/// in a fork and adds the created thread to the list passed as argument in the continuation
let rec many (n:nat) (threads:list (T.thread emp))
  : SteelT unit emp (fun _ -> emp)
  = if n = 0 then join_all threads
    else T.fork client_server (fun t _ -> many (n-1) (t::threads))
