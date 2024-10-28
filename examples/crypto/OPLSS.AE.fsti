(*
   Copyright 2008-2018 Microsoft Research

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
module OPLSS.AE
(* This is the interface for authenticated encryption (AE)

   It provides an ideal view of AE in terms of a log associating
   plain and ciphertexts.

   However, this ideal interface is implemented without any loss in
   security by composing secure interfaces for MACs (based on the
   UF-CMA hypothesis) and Encryption (based on IND-CPA).
*)
open OPLSS //some basic definitions for this demo
open FStar.Seq //F* library of sequences
module HS = FStar.HyperStack //The memory model
open FStar.HyperStack.ST //The State effect over that memory model
module B = LowStar.Monotonic.Buffer //Arrays, abstract locations, framing etc.

/// `key`: An abstract type of AE keys
val key : Type u#0

/// `ae_cipher`: An abstract type of AE ciphers
val ae_cipher : eqtype

/// The abstract memory footprint of key is just an abstract
/// "location", i.e., `B.loc`
///
/// The function has effect `GTot`, meaning it is "Ghost" or
/// computationally irrelevant, i.e., for specification only
val footprint (k:key) : GTot B.loc

/// We have an abstract invariant relating keys to memorys
val invariant : key -> HS.mem -> prop

/// Each element in the ae log associates a plain and a cipher text
let log_entry = Plain.plain & ae_cipher

/// ae_log: given a key and a memory (satisfying the invariant)
/// we can (for spec purposes) read the log of entries
val ae_log (k:key) (h:HS.mem{invariant k h})
  : GTot (Seq.seq log_entry)

/// keygen: create a fresh key
///         When idealizing, its ae log is initially empty
val keygen (_:unit)
  : ST key
  (requires fun _ -> True)
  (ensures  fun h0 k h1 ->
    B.modifies B.loc_none h0 h1 /\
    invariant k h1 /\
    (Flag.reveal Ideal.ae ==> ae_log k h1 == Seq.empty))

/// encrypt:
///       We return a cipher, preserve the invariant,
///       and extend the log by exactly one entry
val encrypt (k:key) (plain:Plain.plain)
  : ST ae_cipher
  (requires
    invariant k)
  (ensures  fun h0 c h1 ->
    invariant k h1 /\
    B.modifies (footprint k) h0 h1 /\
     (Flag.reveal Ideal.ae ==> ae_log k h1 == Seq.snoc (ae_log k h0) (plain, c)))

/// decrypt:
///     In the ideal case, we prove it functionally correct and
///     secure meaning that the plain text returned is exactly the one
///     in the AE log
val decrypt (k:key) (c:ae_cipher)
  : ST (option Plain.plain)
  (requires
    invariant k)
  (ensures fun h0 res h1 ->
    invariant k h1 /\
    h0 == h1 /\
    (Flag.reveal Ideal.ae && Some? res ==> ae_log k h1 `Log.has` (Some?.v res, c)))
