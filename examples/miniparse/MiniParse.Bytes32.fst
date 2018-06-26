module MiniParse.Bytes32
include FStar.Bytes

module U32 = FStar.UInt32

(* TODO: move to FStar.Bytes *)

inline_for_extraction
let b32slice
  (b: bytes)
  (s: U32.t)
  (e: U32.t)
: Pure bytes
  (requires (U32.v s <= U32.v e /\ U32.v e <= length b))
  (ensures (fun res -> reveal res == Seq.slice (reveal b) (U32.v s) (U32.v e)))
= slice b s e

inline_for_extraction
let b32append
  (b1: bytes)
  (b2: bytes)
: Pure bytes
  (requires (length b1 + length b2 < 4294967296))
  (ensures (fun y -> reveal y == Seq.append (reveal b1) (reveal b2)))
= append b1 b2

let b32_index_reveal
  (b: bytes)
  (i: nat { i < length b })
: Lemma
  (Seq.index (reveal b) i == index b i)
= ()

let b32_reveal_create
  (len: U32.t)
  (v: byte)
: Lemma
  (reveal (create len v) == Seq.create (U32.v len) v)
  [SMTPat (reveal (create len v))]
= let b = create len v in
  let lhs = reveal b in
  let rhs = Seq.create (U32.v len) v in
  let pty = (i: nat { i < Seq.length lhs }) in
  let post
    (i: pty)
  : GTot Type0
  = Seq.index lhs (i <: nat) == Seq.index rhs (i <: nat)
  in
  let f
    (i: pty)
  : Lemma
    (post i)
  = assert (get b (U32.uint_to_t i) == v)
  in
  Classical.forall_intro #pty #post f;
  Seq.lemma_eq_intro lhs rhs;
  Seq.lemma_eq_elim lhs rhs

let reveal_empty () : Lemma
  (reveal empty_bytes == Seq.createEmpty)
= assert (Seq.equal (reveal empty_bytes) Seq.createEmpty)
