module Plain

open FStar.HyperHeap
open FStar.HyperStack
open FStar.HST
open FStar.UInt32
open FStar.Ghost
open Buffer.Utils
open Crypto.Symmetric.Bytes

// Experiment with abstraction for stack-based secret plaintexts
// for now we assume public lengths and no padding

// Type abstraction protects against aliasing inasmuch
// as it is enforced from allocation.

//16-09-16 STATUS: verifying; used in Crypto.AEAD.Chacha20Poly1305.Ideal


// LIBRARY STUFF


// SECRETS, HIGH AND LOW

type aead_cipher =
  | AES_256_GCM
  | CHACHA20_POLY1305

type id = {
  cipher: aead_cipher;
  uniq: UInt32.t // we'll need more
}

type mac_alg =
  | POLY1305
  | GHASH

let mac_alg_of_id (id: Plain.id): alg =
  match id.cipher with
  | AES_256_GCM -> GHASH
  | CHACHA20_POLY1305 -> POLY1305

assume val authId: i:id -> Tot bool

// -----------------------------------------------------------------------------

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

val slice: #i:id -> #l:plainLen -> p:plain i l -> s:nat -> j:nat{s <= j && j <= l} -> Tot (plain i (j - s))
let slice #i #l p s j = Seq.slice p s j
//16-10-03 TODO add ghost spec

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

let live #i #l h (p:plainBuffer i l) = Buffer.live h (bufferT p)

let create (i:id) (zero:UInt8.t) (len:UInt32.t) :
   StackInline (plainBuffer i (v len))
     (requires (fun h -> is_stack_region h.tip))
     (ensures (fun (h0:mem) p h1 ->
       let b = bufferT p in
       let open FStar.Buffer in
         ~(contains h0 b)
       /\ live h1 p /\ idx b = 0 /\ length b = v len
       /\ frameOf b = h0.tip
       /\ Map.domain h1.h == Map.domain h0.h
       /\ modifies_0 h0 h1
       /\ as_seq h1 b == Seq.create (v len) zero
       ))
 = Buffer.create zero len

let sub #id #l (b:plainBuffer id l)
               (i:UInt32.t{FStar.Buffer (v i + v (bufferT b).idx) < pow2 n})
               (len:UInt32.t{FStar.Buffer (v len <= length (bufferT b) /\ v i + v len <= length (bufferT b))}) : Tot (b':plainBuffer id (v len))
  = Buffer.sub b i len
// ...


// conditional access
val bufferRepr: #i:id {~(authId i)} -> #l:plainLen -> b:plainBuffer i l -> Tot (b':lbuffer l{ b' == bufferT b})
let bufferRepr #i #l b = b
// not sure how to write modifies clauses including plain and plainBuffer

// unconditional ghost access
// should be as_seq
val sel_plain: h:mem -> #i:id -> l:UInt32.t -> buf:plainBuffer i (v l){live h buf} -> GTot (plain i (v l))
let sel_plain h #i l buf = sel_bytes h l buf

val load: #i:id -> l:UInt32.t -> buf: plainBuffer i (v l) -> ST (plain i (v l))
  (requires (fun h0 -> live h0 buf))
  (ensures (fun h0 r h1 -> h0 == h1 /\ live h0 buf /\ sel_plain h1 l buf == r))

let load #i l buf = load_bytes l buf

val store: #i:id -> l:UInt32.t -> buf: plainBuffer i (v l) -> b:plain i (v l) -> ST unit
  (requires (fun h0 -> live h0 buf))
  (ensures (fun h0 r h1 -> live h1 buf /\ Buffer.modifies_1 (bufferT #i #(v l) buf) h0 h1 /\
    sel_plain h1 l buf == b
  ))
let store #i l buf b = store_bytes l buf b

