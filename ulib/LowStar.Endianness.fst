module LowStar.Endianness

/// Stateful operations between machine integers and buffers of uint8s. Most of
/// these operations are implemented natively using the target's system endianness
/// headers, relying on macros or static inline declarations.
///
/// .. note::
///
///    This module supersedes ``C.Endianness``.

module B = LowStar.Monotonic.Buffer

open FStar.HyperStack.ST
open FStar.Endianness
open LowStar.BufferOps

module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module U128 = FStar.UInt128

module HS = FStar.HyperStack

type u8 = U8.t
type u16 = U16.t
type u32 = U32.t
type u64 = U64.t
type u128 = U128.t

/// Byte-swapping operations
/// ------------------------
///
/// TODO these are totally unspecified

assume val htole16: u16 -> u16
assume val le16toh: u16 -> u16

assume val htole32: u32 -> u32
assume val le32toh: u32 -> u32

assume val htole64: u64 -> u64
assume val le64toh: u64 -> u64

assume val htobe16: u16 -> u16
assume val be16toh: u16 -> u16

assume val htobe32: u32 -> u32
assume val be32toh: u32 -> u32

assume val htobe64: u64 -> u64
assume val be64toh: u64 -> u64

/// Precondition for store functions
///
/// Parametrized by the predicate that different store functions can pass accordingly
///
/// Typically saying sequence contents are le_to_n or be_to_n etc.

unfold let store_pre
  (#a:Type) (#rrel #rel:B.srel a) (b:B.mbuffer a rrel rel)
  (i:nat) (j:nat{i + j <= B.length b}) (predicate:Seq.seq a -> Type0)
  = fun (h:HS.mem) ->
    let sb = B.as_seq h b in
    let len = B.length b in

    B.live h b /\

    (forall (s:Seq.seq a).  //monotonicity precondition that once the contents of the buffer
                       //between [i, j) are replaced as per the predicate, the preorder rel is satisfied

       (Seq.length s == len  /\
        Seq.equal (Seq.slice s 0 i) (Seq.slice sb 0 i) /\
        Seq.equal (Seq.slice s (i + j) len) (Seq.slice sb (i + j) len) /\
        predicate (Seq.slice s i (i + j)))

       ==> rel sb s)


/// Common postcondition

unfold let store_post
  (#a:Type) (#rrel #rel:B.srel a) (b:B.mbuffer a rrel rel)
  (i:nat) (j:nat{i + j <= B.length b}) (predicate:Seq.seq a -> Type0)
   = fun (h0:HS.mem) (_:unit) (h1:HS.mem) ->
     B.live h1 b /\
     B.(modifies (loc_buffer b) h0 h1) /\
     (let s1 = B.as_seq h0 b in
      let s2 = B.as_seq h1 b in
      let len = B.length b in

      //the buffer only changes in the interval [i, j) as per the predicate
      Seq.equal (Seq.slice s2 0 i) (Seq.slice s1 0 i) /\
      Seq.equal (Seq.slice s2 (i + j) len) (Seq.slice s1 (i + j) len) /\
      predicate (Seq.slice s2 i (i + j)))


/// Loads and stores
/// ----------------
///
/// These are primitive

assume val store16_le
  (#rrel #rel:B.srel u8) (b:B.mbuffer u8 rrel rel)
  (i:u32{U32.v i + 2 <= B.length b})
  (z:u16)
  : Stack unit
      (requires (store_pre  b (U32.v i) 2 (fun s -> le_to_n s == U16.v z)))
      (ensures  (store_post b (U32.v i) 2 (fun s -> le_to_n s == U16.v z)))

assume val load16_le
  (#rrel #rel:B.srel u8) (b:B.mbuffer u8 rrel rel)
  (i:u32{U32.v i + 2 <= B.length b})
  : Stack u16
      (requires fun h -> B.live h b)
      (ensures  fun h0 z h1 ->
        h0 == h1 /\
        B.live h1 b /\
        le_to_n (Seq.slice (B.as_seq h1 b) (U32.v i) (U32.v i + 2)) == U16.v z)

assume val store16_be
  (#rrel #rel:B.srel u8) (b:B.mbuffer u8 rrel rel)
  (i:u32{U32.v i + 2 <= B.length b})
  (z:u16)
  : Stack unit
      (requires (store_pre  b (U32.v i) 2 (fun s -> be_to_n s == U16.v z)))
      (ensures  (store_post b (U32.v i) 2 (fun s -> be_to_n s == U16.v z)))

assume val load16_be
  (#rrel #rel:B.srel u8) (b:B.mbuffer u8 rrel rel)
  (i:u32{U32.v i + 2 <= B.length b})
  : Stack u16
      (requires fun h -> B.live h b)
      (ensures  fun h0 z h1 ->
        h0 == h1 /\
        B.live h1 b /\
        be_to_n (Seq.slice (B.as_seq h1 b) (U32.v i) (U32.v i + 2)) == U16.v z)

assume val store32_le
  (#rrel #rel:B.srel u8) (b:B.mbuffer u8 rrel rel)
  (i:u32{U32.v i + 4 <= B.length b})
  (z:u32)
  : Stack unit
      (requires (store_pre  b (U32.v i) 4 (fun s -> le_to_n s == U32.v z)))
      (ensures  (store_post b (U32.v i) 4 (fun s -> le_to_n s == U32.v z)))

assume val load32_le
  (#rrel #rel:B.srel u8) (b:B.mbuffer u8 rrel rel)
  (i:u32{U32.v i + 4 <= B.length b})
  : Stack u32
      (requires fun h -> B.live h b)
      (ensures  fun h0 z h1 ->
        h0 == h1 /\
        B.live h1 b /\
        le_to_n (Seq.slice (B.as_seq h1 b) (U32.v i) (U32.v i + 4)) == U32.v z)

assume val store32_be
  (#rrel #rel:B.srel u8) (b:B.mbuffer u8 rrel rel)
  (i:u32{U32.v i + 4 <= B.length b})
  (z:u32)
  : Stack unit
      (requires (store_pre  b (U32.v i) 4 (fun s -> be_to_n s == U32.v z)))
      (ensures  (store_post b (U32.v i) 4 (fun s -> be_to_n s == U32.v z)))

assume val load32_be
  (#rrel #rel:B.srel u8) (b:B.mbuffer u8 rrel rel)
  (i:u32{U32.v i + 4 <= B.length b})
  : Stack u32
      (requires fun h -> B.live h b)
      (ensures  fun h0 z h1 ->
        h0 == h1 /\
        B.live h1 b /\
        be_to_n (Seq.slice (B.as_seq h1 b) (U32.v i) (U32.v i + 4)) == U32.v z)

assume val store64_le
  (#rrel #rel:B.srel u8) (b:B.mbuffer u8 rrel rel)
  (i:u32{U32.v i + 8 <= B.length b})
  (z:u64)
  : Stack unit
      (requires (store_pre  b (U32.v i) 8 (fun s -> le_to_n s == U64.v z)))
      (ensures  (store_post b (U32.v i) 8 (fun s -> le_to_n s == U64.v z)))

assume val load64_le
  (#rrel #rel:B.srel u8) (b:B.mbuffer u8 rrel rel)
  (i:u32{U32.v i + 8 <= B.length b})
  : Stack u64
      (requires fun h -> B.live h b)
      (ensures  fun h0 z h1 ->
        h0 == h1 /\
        B.live h1 b /\
        le_to_n (Seq.slice (B.as_seq h1 b) (U32.v i) (U32.v i + 8)) == U64.v z)

assume val store64_be
  (#rrel #rel:B.srel u8) (b:B.mbuffer u8 rrel rel)
  (i:u32{U32.v i + 8 <= B.length b})
  (z:u64)
  : Stack unit
      (requires (store_pre  b (U32.v i) 8 (fun s -> be_to_n s == U64.v z)))
      (ensures  (store_post b (U32.v i) 8 (fun s -> be_to_n s == U64.v z)))

assume val load64_be
  (#rrel #rel:B.srel u8) (b:B.mbuffer u8 rrel rel)
  (i:u32{U32.v i + 8 <= B.length b})
  : Stack u64
      (requires fun h -> B.live h b)
      (ensures  fun h0 z h1 ->
        h0 == h1 /\
        B.live h1 b /\
        be_to_n (Seq.slice (B.as_seq h1 b) (U32.v i) (U32.v i + 8)) == U64.v z)

assume val store128_le
  (#rrel #rel:B.srel u8) (b:B.mbuffer u8 rrel rel)
  (i:u32{U32.v i + 16 <= B.length b})
  (z:u128)
  : Stack unit
      (requires (store_pre  b (U32.v i) 16 (fun s -> le_to_n s == U128.v z)))
      (ensures  (store_post b (U32.v i) 16 (fun s -> le_to_n s == U128.v z)))

assume val load128_le
  (#rrel #rel:B.srel u8) (b:B.mbuffer u8 rrel rel)
  (i:u32{U32.v i + 16 <= B.length b})
  : Stack u128
      (requires fun h -> B.live h b)
      (ensures  fun h0 z h1 ->
        h0 == h1 /\
        B.live h1 b /\
        le_to_n (Seq.slice (B.as_seq h1 b) (U32.v i) (U32.v i + 16)) == U128.v z)

assume val store128_be
  (#rrel #rel:B.srel u8) (b:B.mbuffer u8 rrel rel)
  (i:u32{U32.v i + 16 <= B.length b})
  (z:u128)
  : Stack unit
      (requires (store_pre  b (U32.v i) 16 (fun s -> be_to_n s == U128.v z)))
      (ensures  (store_post b (U32.v i) 16 (fun s -> be_to_n s == U128.v z)))


assume val load128_be
  (#rrel #rel:B.srel u8) (b:B.mbuffer u8 rrel rel)
  (i:u32{U32.v i + 16 <= B.length b})
  : Stack u128
      (requires fun h -> B.live h b)
      (ensures  fun h0 z h1 ->
        h0 == h1 /\
        B.live h1 b /\
        be_to_n (Seq.slice (B.as_seq h1 b) (U32.v i) (U32.v i + 16)) == U128.v z)


/// Index and update
/// ----------------
///
/// These are more sophisticated than load/store above, because they reason
/// over the underlying sequence of bytes interpreted as a sequence of (little|big)-endian
/// integers.

#set-options "--z3rlimit 20 --max_fuel 0 --max_ifuel 0"

inline_for_extraction
let index_32_be
  (#rrel #rel:B.srel u8) (b:B.mbuffer u8 rrel rel)
  (i:u32)
  : Stack u32
      (requires fun h ->
        B.live h b /\ B.length b % 4 = 0 /\
        U32.v i < B.length b / 4)
      (ensures fun h0 r h1 ->
        h0 == h1 /\
        r = Seq.index (seq_uint32_of_be (B.length b / 4) (B.as_seq h0 b)) (U32.v i))
  = load32_be b FStar.UInt32.(4ul *^ i)

inline_for_extraction
let index_32_le
  (#rrel #rel:B.srel u8) (b:B.mbuffer u8 rrel rel)
  (i:u32)
  : Stack u32
      (requires fun h ->
        B.live h b /\ B.length b % 4 = 0 /\
        U32.v i < B.length b / 4)
      (ensures fun h0 r h1 ->
        h0 == h1 /\
        r = Seq.index (seq_uint32_of_le (B.length b / 4) (B.as_seq h0 b)) (U32.v i))
  = load32_le b FStar.UInt32.(4ul *^ i)

inline_for_extraction
let index_64_be
  (#rrel #rel:B.srel u8) (b:B.mbuffer u8 rrel rel)
  (i:u32)
  : Stack u64
      (requires fun h ->
        B.live h b /\ B.length b % 8 = 0 /\
        U32.v i < B.length b / 8)
      (ensures fun h0 r h1 ->
        h0 == h1 /\
        r = Seq.index (seq_uint64_of_be (B.length b / 8) (B.as_seq h0 b)) (UInt32.v i))
  = load64_be b FStar.UInt32.(8ul *^ i)

inline_for_extraction
let index_64_le
  (#rrel #rel:B.srel u8) (b:B.mbuffer u8 rrel rel)
  (i:u32)
  : Stack u64
      (requires fun h ->
        B.live h b /\ B.length b % 8 = 0 /\
        U32.v i < B.length b / 8)
      (ensures fun h0 r h1 ->
        h0 == h1 /\
        r = Seq.index (seq_uint64_of_le (B.length b / 8) (B.as_seq h0 b)) (UInt32.v i))
  = load64_le b FStar.UInt32.(8ul *^ i)

#reset-options "--using_facts_from 'Prims'"

let interval_4_disjoint (i j: nat)
  : Lemma
    (requires (i <> j))
    (ensures  (let open FStar.Mul in 4 * i + 4 <= 4 * j \/ 4 * j + 4 <= 4 * i))
  = ()

#reset-options "--z3rlimit 16 --max_fuel 0 --max_ifuel 0"

inline_for_extraction
let upd_32_be
  (#rrel #rel:B.srel u8) (b:B.mbuffer u8 rrel rel)
  (i:u32) (v:u32)
  : Stack unit
     (requires fun h ->
       B.length b % 4 = 0 /\
       U32.v i < B.length b / 4 /\
       store_pre b (U32.(v (4ul *^ i))) 4 (fun s -> be_to_n s == U32.v v) h)
     (ensures fun h0 _ h1 ->
       B.(modifies (loc_buffer b) h0 h1) /\
       seq_uint32_of_be (B.length b / 4) (B.as_seq h1 b) `Seq.equal` Seq.upd (seq_uint32_of_be (B.length b / 4) (B.as_seq h0 b)) (U32.v i) v)

  = let h0 = get () in
    store32_be b U32.(4ul *^ i) v;
    let h1 = get () in

    //AR: 03/01: the following 3 assertions say how the buffer changed
    assert (be_to_n (Seq.slice (B.as_seq h1 b) (U32.(v (4ul *^ i))) (U32.(v (4ul *^ i) + 4))) == U32.v v);
    assert (Seq.equal (Seq.slice (B.as_seq h0 b) 0 (U32.(v (4ul *^ i))))
                      (Seq.slice (B.as_seq h1 b) 0 (U32.(v (4ul *^ i)))));
    assert (Seq.equal (Seq.slice (B.as_seq h0 b) (U32.(v (4ul *^ i) + 4)) (B.length b))
                      (Seq.slice (B.as_seq h1 b) (U32.(v (4ul *^ i) + 4)) (B.length b)));

    let f () : Lemma
      (seq_uint32_of_be (B.length b / 4) (B.as_seq h1 b) `Seq.equal` Seq.upd (seq_uint32_of_be (B.length b / 4) (B.as_seq h0 b))
                        (UInt32.v i) v)
    = let s0 = B.as_seq h0 b in
      let s1 = B.as_seq h1 b in
    let n = B.length b / 4 in
    assert (4 `Prims.op_Multiply` n == B.length b);
    let s0' = seq_uint32_of_be n s0 in
    let s1' = seq_uint32_of_be n s1 in
    let lo = UInt32.v i in
    let hi = lo + 1 in
    let s2' = Seq.upd s0' lo v in
    assert (Seq.length s1' == Seq.length s2');
    let f
      (j: nat)
    : Lemma
      (requires (j < n))
      (ensures (j < n /\ Seq.index s1' j == Seq.index s2' j))
    =
      if j = lo
      then ()
      else begin
        slice_seq_uint32_of_be n s0 j (j + 1);
        slice_seq_uint32_of_be n s1 j (j + 1);
	let init = U32.v (4ul `UInt32.mul` UInt32.uint_to_t j) in
        let sj0 = seq_uint32_of_be 1 (Seq.slice (B.as_seq h0 b) init (init + 4)) in
        let sj1 = seq_uint32_of_be 1 (Seq.slice (B.as_seq h1 b) init (init + 4)) in
        assert (Seq.index s1' j == Seq.index sj1 0);
        assert (Seq.index s0' j == Seq.index sj0 0);
        interval_4_disjoint j lo;
        admit ()  //AR: 03/01: TODO
      end
    in
    Classical.forall_intro (Classical.move_requires f)
  in
  f ()
