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
open OPLSS
open FStar.Seq
open FStar.HyperStack.ST
module B = LowStar.Monotonic.Buffer
module HS = FStar.HyperStack

val key : Type u#0

let ae_cipher = AES.iv_cipher * HMACSHA1.tag

val footprint (k:key) : GTot B.loc

val invariant : key -> HS.mem -> prop

let log_entry = Plain.plain & ae_cipher

val ae_log (k:key) (h:HS.mem{invariant k h})
  : GTot (Seq.seq log_entry)

/// keygen: create a fresh key
///         its ae log is initially empty
val keygen (_:unit)
  : ST key
  (requires fun _ -> True)
  (ensures  fun h0 k h1 ->
    B.modifies B.loc_none h0 h1 /\
    invariant k h1 /\
    (Flag.reveal Ideal.uf_cma ==> ae_log k h1 == Seq.empty))

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
    (Flag.reveal Ideal.uf_cma ==> ae_log k h1 == Seq.snoc (ae_log k h0) (plain, c)))

/// decrypt:
///     In the ideal case, we prove it functionally correct and secure
///     meaning that we the plain text returned is exactly the one in in AE log
val decrypt (k:key) (c:ae_cipher)
  : ST (option Plain.plain)
  (requires
    invariant k)
  (ensures fun h0 res h1 ->
    invariant k h1 /\
    h0 == h1 /\
    (Flag.reveal Ideal.uf_cma && Some? res ==> ae_log k h1 `Log.has` (Some?.v res, c)))
