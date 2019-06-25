module OPLSS.Encrypt
module UInt8 = FStar.UInt8
module Log = OPLSS.Log
module Ideal = EtM.Ideal
module B = LowStar.Monotonic.Buffer
open FStar.HyperStack.ST
module HS = FStar.HyperStack
let bytes = Seq.seq UInt8.t

type log_entry =
  | Entry : msg:bytes -> cipher:bytes -> log_entry

let raw_key = bytes

noeq
type key =
  | Key: raw:raw_key
       -> log:Log.t log_entry
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
    let l = Log.new_log #log_entry in
    Key raw l
