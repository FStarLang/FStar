module OPLSS.MAC
module UInt8 = FStar.UInt8
module Log = OPLSS.Log
module Ideal = OPLSS.Ideal
module B = LowStar.Monotonic.Buffer
open FStar.HyperStack.ST
module HS = FStar.HyperStack
let bytes = Seq.seq UInt8.t

let raw_key = bytes
let msg = bytes
let tag = bytes

assume
val hmac_sha1 : raw_key -> bytes -> bytes

type log_entry =
  | Entry : msg:bytes -> tag:bytes -> log_entry

noeq
type key =
  | Key: raw:raw_key
       -> log:Log.t log_entry
       -> key

let loc (k:key) = B.loc_mreference k.log
let log (k:key) (h:HS.mem) = Log.entries k.log h

assume
val random : unit -> EXT raw_key

let invariant (k:key) (h:HS.mem) : Type =
  HS.contains h k.log

let keygen () :
  ST key
  (requires fun _ -> True)
  (ensures fun h0 k h1 ->
    invariant k h1 /\
    B.modifies B.loc_none h0 h1 /\
    B.fresh_loc (B.loc_mreference k.log) h0 h1 /\
    log k h1 == Seq.empty)
  = let raw = random () in
    let l = Log.new_log #log_entry in
    Key raw l

let mac (k:key) (m:msg)
  : ST tag
    (requires
      invariant k)
    (ensures fun h0 t h1 ->
      invariant k h1 /\
      B.modifies (B.loc_mreference k.log) h0 h1 /\
      t == hmac_sha1 k.raw m /\
      (if Ideal.uf_cma
       then log k h1 == Seq.snoc (log k h0) (Entry m t)
       else log k h1 == log k h0))
  = let t = hmac_sha1 k.raw m in
    if Ideal.uf_cma then Log.add k.log (Entry m t);
    t

let verify (k:key) (m:msg) (t:tag)
  : ST bool
    (requires
      invariant k)
    (ensures fun h0 b h1 ->
      invariant k h1 /\
      h0 == h1 /\
      (b ==> t == hmac_sha1 k.raw m /\
             (Ideal.uf_cma ==> log k h1 `Log.has` Entry m t)))
  = let verified = (t = hmac_sha1 k.raw m) in
    if Ideal.uf_cma
    then let found = Some? (Log.find k.log (fun e -> e.msg = m && e.tag = t)) in
         verified && found
    else verified
