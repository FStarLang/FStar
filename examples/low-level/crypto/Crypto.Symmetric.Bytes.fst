module Crypto.Symmetric.Bytes

open FStar.HyperHeap
open FStar.HyperStack
open FStar.HST
open FStar.UInt32
open FStar.Ghost
open Buffer.Utils


type mem = FStar.HyperStack.mem

type bytes = Seq.seq UInt8.t 
type buffer = Buffer.buffer UInt8.t 

type lbytes (l:nat)  = b:bytes  {Seq.length b = l}
type lbuffer (l:nat) = b:buffer {Buffer.length b = l}

val sel_bytes: h:mem -> l:UInt32.t -> buf:lbuffer(v l){Buffer.live h buf}
  -> GTot (lbytes (v l))
let sel_bytes h l buf = Buffer.as_seq h buf

val load_bytes: l:UInt32.t -> buf:lbuffer(v l) -> Stack (lbytes(v l))
  (requires (fun h0 -> Buffer.live h0 buf))
  (ensures  (fun h0 r h1 -> h0 == h1 /\ Buffer.live h0 buf /\ r == sel_bytes h1 l buf))
let rec load_bytes l buf = 
//  assume false;//16-09-21 TODO 
  if l = 0ul then Seq.createEmpty else
  let b = Buffer.index buf 0ul in
  let t = load_bytes (l -^ 1ul) (Buffer.sub buf 1ul (l -^ 1ul)) in
  SeqProperties.cons b t


val store_bytes: l:UInt32.t -> buf:lbuffer(v l) -> b:lbytes(v l) -> ST unit
  (requires (fun h0 -> Buffer.live h0 buf))
  (ensures (fun h0 r h1 -> Buffer.live h1 buf /\ Buffer.modifies_1 buf h0 h1 /\ b == sel_bytes h1 l buf
  ))

val store_bytes_aux: len:UInt32.t -> buf:lbuffer(v len) -> i:UInt32.t  {i <=^ len} -> b:lbytes(v len) -> ST unit
  (requires (fun h0 -> Buffer.live h0 buf))
  (ensures (fun h0 r h1 -> Buffer.live h1 buf /\ Buffer.modifies_1 buf h0 h1 /\ b == sel_bytes h1 len buf
  ))
let rec store_bytes_aux len buf i b = 
  assume false;//16-09-21 TODO 
  if i <^ len then (
  Buffer.upd buf i (Seq.index b (v i));
  store_bytes_aux len buf (i +^ 1ul) b)
let store_bytes l buf b = store_bytes_aux l buf 0ul b
