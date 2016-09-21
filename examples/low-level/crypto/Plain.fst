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

type mem = FStar.HyperStack.mem

let modifies_1 = Buffer.modifies_1

type bytes = Seq.seq UInt8.t 
type buffer = Buffer.buffer UInt8.t 

type lbytes (l:nat)  = b:bytes  {Seq.length b = l}
type lbuffer (l:nat) = b:buffer {Buffer.length b = l}

assume val sel_bytes: h:mem -> l:UInt32.t -> buf:lbuffer(v l){Buffer.live h buf}  -> Tot (lbytes (v l))

//TODO add functional correctness
assume val load_bytes: l:UInt32.t -> buf:lbuffer(v l) -> Stack (lbytes(v l))
  (requires (fun h0 -> Buffer.live h0 buf))
  (ensures (fun h0 r h1 -> h0 == h1 /\ Buffer.live h0 buf /\ r == sel_bytes h1 l buf))
assume val store_bytes: l:UInt32.t -> buf:lbuffer(v l) -> b:lbytes(v l) -> ST unit
  (requires (fun h0 -> Buffer.live h0 buf))
  (ensures (fun h0 r h1 -> Buffer.live h1 buf /\ modifies_1 buf h0 h1 /\ b == sel_bytes h1 l buf
  ))

// SECRETS, HIGH AND LOW

type id = UInt32.t // we'll need more
assume val authId: i:id -> Tot bool

type plainLen = nat // we'll need a tigher bound

abstract type plain (i:id) (l:plainLen) = lbytes l

// to be restricted
val repr: #i:id -> #l:plainLen -> p:plain i l -> Tot (lbytes l)
let repr #i #l p = p

val make: #i:id -> l:plainLen -> b:lbytes l -> Tot (plain i l)
let make #i l b = b

val reveal: #i:id -> #l:plainLen -> p:plain i l -> GTot (lbytes l)
let reveal #i #l p = p

val reveal_injective : i:id -> l:plainLen -> p:plain i l -> Lemma
  (requires True)
  (ensures (make #i l (reveal p) == p))
  [SMTPat (reveal p)]
let reveal_injective i l p = ()

abstract type plainBuffer (i:id) (l:plainLen) = b:lbuffer l

val hide_buffer: i:id -> #l:plainLen -> b:lbuffer l -> GTot (plainBuffer i l)
let hide_buffer i #l b = b

val bufferT: #i:id -> #l:plainLen -> b:plainBuffer i l -> GTot (lbuffer l)
let bufferT #i #l b = b

val bufferT_injective : i:id -> l:plainLen -> p:plainBuffer i l -> Lemma
  (requires True)
  (ensures (hide_buffer i (bufferT p) == p))
  [SMTPat (bufferT p)]
let bufferT_injective i l p = ()

let live #i #l h (p:plainBuffer i l) = Buffer.live h p

let create (i:id) (zero:UInt8.t) (l:UInt32.t): plainBuffer i (v l) = Buffer.create zero l 

open FStar.Buffer // for .idx
let sub #id #l (b:plainBuffer id l) 
	       (i:UInt32.t{v i + v (bufferT b).idx < pow2 n}) 
	       (len:UInt32.t{v len <= length (bufferT b) /\ v i + v len <= length (bufferT b)}) : Tot (b':plainBuffer id (v len))
  = sub b i len
// ...

val bufferRepr: #i:id {~(authId i)} -> #l:plainLen -> b:plainBuffer i l -> Tot (b':lbuffer l{ b' == bufferT b})
let bufferRepr #i #l b = b
// not sure how to write modifies clauses including plain and plainBuffer

val sel_plain: h:mem -> #i:id -> l:UInt32.t -> buf:plainBuffer i (v l){live h buf} -> Tot (plain i (v l)) 
let sel_plain h #i l buf = sel_bytes h l buf

val load: #i:id -> l:UInt32.t -> buf: plainBuffer i (v l) -> ST (plain i (v l)) 
  (requires (fun h0 -> live h0 buf))
  (ensures (fun h0 r h1 -> h0 == h1 /\ live h0 buf /\ sel_plain h1 l buf == repr r))

let load #i l buf = load_bytes l buf

val store: #i:id -> l:UInt32.t -> buf: plainBuffer i (v l) -> b:plain i (v l) -> ST unit
  (requires (fun h0 -> live h0 buf))
  (ensures (fun h0 r h1 -> live h1 buf /\ modifies_1 (bufferT #i #(v l) buf) h0 h1 /\
    sel_plain h1 l buf == repr b
  ))
let store #i l buf b = 
  // assume false; // TODO, not sure what's missing here
  store_bytes l buf b

