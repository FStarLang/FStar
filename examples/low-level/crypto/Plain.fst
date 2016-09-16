module Plain 

open FStar.HyperHeap
open FStar.HyperStack
open FStar.HST
open FStar.UInt32
open FStar.Ghost
open Buffer.Utils

// Experiment with abstraction for stack-based secret plaintexts
// for now we assume public lengths and no padding

// Type abstraction protects against aliasing inasmuch 
// as it is enforced from allocation. 

//16-09-16 STATUS: verifying; used in Crypto.AEAD.Chacha20Poly1305.Ideal 


// LIBRARY STUFF

let modifies_1 = Buffer.modifies_1

type bytes = Seq.seq UInt8.t 
type buffer = Buffer.buffer UInt8.t 

type lbytes (l:nat)  = b:bytes  {Seq.length b = l}
type lbuffer (l:nat) = b:buffer {Buffer.length b = l}

//TODO add functional correctness
assume val load_bytes: l:UInt32.t -> buf:lbuffer(v l) -> STL (lbytes(v l))
  (requires (fun h0 -> Buffer.live h0 buf))
  (ensures (fun h0 r h1 -> h0 == h1))
assume val store_bytes: l:UInt32.t -> buf:lbuffer(v l) -> lbytes(v l) -> ST unit
  (requires (fun h0 -> Buffer.live h0 buf))
  (ensures (fun h0 r h1 -> Buffer.live h1 buf /\ modifies_1 buf h0 h1))
assume val sel_bytes: h:FStar.HyperHeap.t -> l:UInt32.t -> buf:lbuffer(v l) -> Tot (lbytes (v l))
// how to state that buf is live here?

// SECRETS, HIGH AND LOW

type id = UInt32.t // we'll need more
assume val authId: i:id -> Tot bool

type plainLen = nat // we'll need a tigher bound

abstract type plain (i:id) (l:plainLen) = lbytes l

val repr: #i:id -> #l:plainLen -> p:plain i l -> Tot (lbytes (Seq.length p))
let repr #i #l p = p

val make: #i:id -> l:plainLen -> b:lbytes l -> Tot (plain i l)
let make #i l b = b

open FStar.Buffer 

abstract type plainBuffer (i:id) (l:plainLen) = b:lbuffer l

let live #i #l h (p:plainBuffer i l) = Buffer.live h p

let create (i:id) (zero:UInt8.t) (l:UInt32.t): plainBuffer i (v l)  = create zero l 

let sub #id #l (b:plainBuffer id l) (i:UInt32.t{v i + v b.idx < pow2 n}) (len:UInt32.t{v len <= length b /\ v i + v len <= length b}) : Tot (b':plainBuffer id (v len))
  = sub b i len
// ...

let load #i l (buf: plainBuffer i (v l)): plain i (v l) = load_bytes l buf
let store #i l (buf: plainBuffer i (v l)) (b: plain i (v l)) : unit = store_bytes l buf b
