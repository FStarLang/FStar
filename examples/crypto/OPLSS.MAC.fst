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
module OPLSS.MAC
(* This module idealizes HMACSHA1 as an UF-CMA MAC *)
open OPLSS
open FStar.HyperStack.ST
module B = LowStar.Monotonic.Buffer
module HS = FStar.HyperStack

/// The UF-CMA log associates messages with tags
type log_entry =
  | Entry: msg:HMACSHA1.msg
         -> tag:HMACSHA1.tag
         -> log_entry

/// A key packages a raw HMACSHA1 key with the ideal UF-CMA log
noeq
type key =
  | Key: raw:HMACSHA1.sha1_key
       -> log:Log.t log_entry
       -> key

let loc (k:key) = B.loc_mreference k.log
let log (k:key) (h:HS.mem) = Log.entries k.log h

/// The invariant is simply that the log is live
let invariant (k:key) (h:HS.mem) : Type =
  HS.contains h k.log

/// Generating a new MAC'ing key
///   - satisfying the invariant
///   - allocating _fresh_ state for the log
///   - intializing it to the empty log
let keygen ()
  : ST key
    (requires fun _ -> True)
    (ensures fun h0 k h1 ->
      invariant k h1 /\
      B.modifies B.loc_none h0 h1 /\
      B.fresh_loc (Log.fp k.log) h0 h1 /\
      log k h1 == Seq.empty)
  = let raw = random HMACSHA1.keysize in
    let l = Log.new_log #log_entry in
    Key raw l

/// `mac k m`:
///   Concretely, it's just HMACSHA1
///   But, ideally, it also appends a new entry in the log
let mac (k:key) (m:HMACSHA1.msg)
  : ST HMACSHA1.tag
    (requires
      invariant k)
    (ensures fun h0 t h1 ->
      invariant k h1 /\
      B.modifies (Log.fp k.log) h0 h1 /\
      t == HMACSHA1.hmac_sha1 k.raw m /\
      (if Flag.reveal Ideal.uf_cma
       then log k h1 == Seq.snoc (log k h0) (Entry m t)
       else log k h1 == log k h0))
  = let t = HMACSHA1.hmac_sha1 k.raw m in
    //CRYPTO HYPOTHESIS
    //    () ~ (Log.add k.log Entry m t)
    //The log is private
    if Flag.idealizing Ideal.uf_cma
    then Log.add k.log (Entry m t);
    t

/// `verify k m`
///   Concretely, just an HMACSHA1 verify
///   Ideally, it corrects for HMACSHA1 collisions using log lookups
let verify (k:key) (m:HMACSHA1.msg) (t:HMACSHA1.tag)
  : ST bool
    (requires
      invariant k)
    (ensures fun h0 b h1 ->
      invariant k h1 /\
      h0 == h1 /\
      (b <==> t == HMACSHA1.hmac_sha1 k.raw m /\
            (Flag.reveal Ideal.uf_cma ==> log k h1 `Log.has` Entry m t)))
  = let verified = (t = HMACSHA1.hmac_sha1 k.raw m) in
    //CRYPTO HYPOTHESIS
    //  Correction of Errors in HMACSHA1 can
    //  only be observed with negligible probability
    if Flag.idealizing Ideal.uf_cma
    then let found = Some? (Log.find k.log (fun e -> e.msg = m && e.tag = t)) in
         verified && found
    else verified
