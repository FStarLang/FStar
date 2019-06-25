module OPLSS.MAC
module UInt8 = FStar.UInt8
module Log = OPLSS.Log
module Ideal = EtM.Ideal
module B = LowStar.Monotonic.Buffer
open FStar.HyperStack.ST
module HS = FStar.HyperStack
let bytes = Seq.seq UInt8.t

let raw_key = bytes
let msg = bytes
let tag = bytes

assume
val hmac_sha1 : raw_key -> bytes -> bytes

type log_entry (k:raw_key) =
  | Entry : msg:bytes -> tag:bytes{tag == hmac_sha1 k msg} -> log_entry k

noeq
type key =
  | Key: raw:raw_key
       -> log:Log.t (log_entry raw)
       -> key

assume
val random : unit -> EXT raw_key

let keygen () :
  ST key
  (requires fun _ -> True)
  (ensures fun h0 k h1 ->
    B.modifies B.loc_none h0 h1 /\
    HS.sel h1 k.log == Seq.empty)
  = let raw = random () in
    let l = Log.new_log #(log_entry raw) in
    Key raw l


let mac (k:key) (m:msg)
  : ST tag
    (requires fun _ -> True)
    (ensures fun h0 t h1 ->
      B.modifies (B.loc_mreference k.log) h0 h1 /\
      t == hmac_sha1 k.raw m /\
      k.log `Log.contains` Entry m t)
  = let t = hmac_sha1 k.raw m in
    Log.add k.log (Entry m t);
    t

let verify (k:key) (m:msg) (t:tag)
  : ST bool
    (requires fun _ -> True)
    (ensures fun h0 b h1 ->
      B.modifies B.loc_none h0 h1 /\
      (b ==> t == hmac_sha1 k.raw m /\ k.log `Log.contains` Entry m t))
  = let verified = (t = hmac_sha1 k.raw m) in
    let found = Some? (Log.find k.log (fun e -> e.msg = m && e.tag = t)) in
    verified && found
