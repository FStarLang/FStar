module LowStar.Endianness

/// Stateful operations between machine integers and buffers of uint8s. Most of
/// these operations are implemented natively using the target's system endianness
/// headers, relying on macros or static inline declarations.
///
/// .. note::
///
///    This module supersedes ``C.Endianness``.

module MB = LowStar.Monotonic.Buffer
module B = LowStar.Buffer

open FStar.HyperStack.ST
open FStar.Endianness
open LowStar.BufferOps

module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module U128 = FStar.UInt128

module HS = FStar.HyperStack

inline_for_extraction
type u8 = U8.t
inline_for_extraction
type u16 = U16.t
inline_for_extraction
type u32 = U32.t
inline_for_extraction
type u64 = U64.t
inline_for_extraction
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
  (#a:Type) (#rrel #rel:MB.srel a) (b:MB.mbuffer a rrel rel)
  (i:nat) (j:nat{i + j <= MB.length b}) (predicate:Seq.seq a -> Type0)
  = fun (h:HS.mem) ->
    let sb = MB.as_seq h b in
    let len = MB.length b in

    MB.live h b /\

    (forall (s:Seq.seq a).  //monotonicity precondition that once the contents of the buffer
                       //between [i, j) are replaced as per the predicate, the
                       //preorder rel is satisfied

       (Seq.length s == len  /\
        Seq.equal (Seq.slice s 0 i) (Seq.slice sb 0 i) /\
        Seq.equal (Seq.slice s (i + j) len) (Seq.slice sb (i + j) len) /\
        predicate (Seq.slice s i (i + j)))

       ==> rel sb s)


/// Common postcondition

unfold let store_post
  (#a:Type) (#rrel #rel:MB.srel a) (b:MB.mbuffer a rrel rel)
  (i:nat) (j:nat{i + j <= MB.length b}) (predicate:Seq.seq a -> Type0)
   = fun (h0:HS.mem) (_:unit) (h1:HS.mem) ->
     MB.live h1 b /\
     MB.(modifies (loc_buffer b) h0 h1) /\
     (let s1 = MB.as_seq h0 b in
      let s2 = MB.as_seq h1 b in
      let len = MB.length b in

      //the buffer only changes in the interval [i, j) as per the predicate
      Seq.equal (Seq.slice s2 0 i) (Seq.slice s1 0 i) /\
      Seq.equal (Seq.slice s2 (i + j) len) (Seq.slice s1 (i + j) len) /\
      predicate (Seq.slice s2 i (i + j)))


/// Loads and stores
/// ----------------
///
/// These are primitive

assume val store16_le_i
  (#rrel #rel:MB.srel u8) (b:MB.mbuffer u8 rrel rel)
  (i:u32{U32.v i + 2 <= MB.length b})
  (z:u16)
  : Stack unit
      (requires (store_pre  b (U32.v i) 2 (fun s -> le_to_n s == U16.v z)))
      (ensures  (store_post b (U32.v i) 2 (fun s -> le_to_n s == U16.v z)))

assume val load16_le_i
  (#rrel #rel:MB.srel u8) (b:MB.mbuffer u8 rrel rel)
  (i:u32{U32.v i + 2 <= MB.length b})
  : Stack u16
      (requires fun h -> MB.live h b)
      (ensures  fun h0 z h1 ->
        h0 == h1 /\
        MB.live h1 b /\
        le_to_n (Seq.slice (MB.as_seq h1 b) (U32.v i) (U32.v i + 2)) == U16.v z)

assume val store16_be_i
  (#rrel #rel:MB.srel u8) (b:MB.mbuffer u8 rrel rel)
  (i:u32{U32.v i + 2 <= MB.length b})
  (z:u16)
  : Stack unit
      (requires (store_pre  b (U32.v i) 2 (fun s -> be_to_n s == U16.v z)))
      (ensures  (store_post b (U32.v i) 2 (fun s -> be_to_n s == U16.v z)))

assume val load16_be_i
  (#rrel #rel:MB.srel u8) (b:MB.mbuffer u8 rrel rel)
  (i:u32{U32.v i + 2 <= MB.length b})
  : Stack u16
      (requires fun h -> MB.live h b)
      (ensures  fun h0 z h1 ->
        h0 == h1 /\
        MB.live h1 b /\
        be_to_n (Seq.slice (MB.as_seq h1 b) (U32.v i) (U32.v i + 2)) == U16.v z)

assume val store32_le_i
  (#rrel #rel:MB.srel u8) (b:MB.mbuffer u8 rrel rel)
  (i:u32{U32.v i + 4 <= MB.length b})
  (z:u32)
  : Stack unit
      (requires (store_pre  b (U32.v i) 4 (fun s -> le_to_n s == U32.v z)))
      (ensures  (store_post b (U32.v i) 4 (fun s -> le_to_n s == U32.v z)))

assume val load32_le_i
  (#rrel #rel:MB.srel u8) (b:MB.mbuffer u8 rrel rel)
  (i:u32{U32.v i + 4 <= MB.length b})
  : Stack u32
      (requires fun h -> MB.live h b)
      (ensures  fun h0 z h1 ->
        h0 == h1 /\
        MB.live h1 b /\
        le_to_n (Seq.slice (MB.as_seq h1 b) (U32.v i) (U32.v i + 4)) == U32.v z)

assume val store32_be_i
  (#rrel #rel:MB.srel u8) (b:MB.mbuffer u8 rrel rel)
  (i:u32{U32.v i + 4 <= MB.length b})
  (z:u32)
  : Stack unit
      (requires (store_pre  b (U32.v i) 4 (fun s -> be_to_n s == U32.v z)))
      (ensures  (store_post b (U32.v i) 4 (fun s -> be_to_n s == U32.v z)))

assume val load32_be_i
  (#rrel #rel:MB.srel u8) (b:MB.mbuffer u8 rrel rel)
  (i:u32{U32.v i + 4 <= MB.length b})
  : Stack u32
      (requires fun h -> MB.live h b)
      (ensures  fun h0 z h1 ->
        h0 == h1 /\
        MB.live h1 b /\
        be_to_n (Seq.slice (MB.as_seq h1 b) (U32.v i) (U32.v i + 4)) == U32.v z)

assume val store64_le_i
  (#rrel #rel:MB.srel u8) (b:MB.mbuffer u8 rrel rel)
  (i:u32{U32.v i + 8 <= MB.length b})
  (z:u64)
  : Stack unit
      (requires (store_pre  b (U32.v i) 8 (fun s -> le_to_n s == U64.v z)))
      (ensures  (store_post b (U32.v i) 8 (fun s -> le_to_n s == U64.v z)))

assume val load64_le_i
  (#rrel #rel:MB.srel u8) (b:MB.mbuffer u8 rrel rel)
  (i:u32{U32.v i + 8 <= MB.length b})
  : Stack u64
      (requires fun h -> MB.live h b)
      (ensures  fun h0 z h1 ->
        h0 == h1 /\
        MB.live h1 b /\
        le_to_n (Seq.slice (MB.as_seq h1 b) (U32.v i) (U32.v i + 8)) == U64.v z)

assume val store64_be_i
  (#rrel #rel:MB.srel u8) (b:MB.mbuffer u8 rrel rel)
  (i:u32{U32.v i + 8 <= MB.length b})
  (z:u64)
  : Stack unit
      (requires (store_pre  b (U32.v i) 8 (fun s -> be_to_n s == U64.v z)))
      (ensures  (store_post b (U32.v i) 8 (fun s -> be_to_n s == U64.v z)))

assume val load64_be_i
  (#rrel #rel:MB.srel u8) (b:MB.mbuffer u8 rrel rel)
  (i:u32{U32.v i + 8 <= MB.length b})
  : Stack u64
      (requires fun h -> MB.live h b)
      (ensures  fun h0 z h1 ->
        h0 == h1 /\
        MB.live h1 b /\
        be_to_n (Seq.slice (MB.as_seq h1 b) (U32.v i) (U32.v i + 8)) == U64.v z)

assume val store128_le_i
  (#rrel #rel:MB.srel u8) (b:MB.mbuffer u8 rrel rel)
  (i:u32{U32.v i + 16 <= MB.length b})
  (z:u128)
  : Stack unit
      (requires (store_pre  b (U32.v i) 16 (fun s -> le_to_n s == U128.v z)))
      (ensures  (store_post b (U32.v i) 16 (fun s -> le_to_n s == U128.v z)))

assume val load128_le_i
  (#rrel #rel:MB.srel u8) (b:MB.mbuffer u8 rrel rel)
  (i:u32{U32.v i + 16 <= MB.length b})
  : Stack u128
      (requires fun h -> MB.live h b)
      (ensures  fun h0 z h1 ->
        h0 == h1 /\
        MB.live h1 b /\
        le_to_n (Seq.slice (MB.as_seq h1 b) (U32.v i) (U32.v i + 16)) == U128.v z)

assume val store128_be_i
  (#rrel #rel:MB.srel u8) (b:MB.mbuffer u8 rrel rel)
  (i:u32{U32.v i + 16 <= MB.length b})
  (z:u128)
  : Stack unit
      (requires (store_pre  b (U32.v i) 16 (fun s -> be_to_n s == U128.v z)))
      (ensures  (store_post b (U32.v i) 16 (fun s -> be_to_n s == U128.v z)))


assume val load128_be_i
  (#rrel #rel:MB.srel u8) (b:MB.mbuffer u8 rrel rel)
  (i:u32{U32.v i + 16 <= MB.length b})
  : Stack u128
      (requires fun h -> MB.live h b)
      (ensures  fun h0 z h1 ->
        h0 == h1 /\
        MB.live h1 b /\
        be_to_n (Seq.slice (MB.as_seq h1 b) (U32.v i) (U32.v i + 16)) == U128.v z)

/// Loads and stores, on buffers of the right size.
/// -----------------------------------------------
///
/// There is bunch of legacy code that wants these operators that operate on buffers of exactly the right size. This is actually more restrictive than the version above, which operates on monotonic buffers, so we offer specialized operators.

let store16_le
  (b:B.buffer UInt8.t{B.length b == 2})
  (z:UInt16.t):
  Stack unit
    (requires (fun h -> B.live h b))
    (ensures  (fun h0 _ h1 -> B.(modifies (loc_buffer b) h0 h1) /\ B.live h1 b /\
                           le_to_n (B.as_seq h1 b) == UInt16.v z))
=
  store16_le_i b 0ul z

let load16_le
  (b:B.buffer UInt8.t{B.length b == 2}):
  Stack UInt16.t
    (requires (fun h -> B.live h b))
    (ensures  (fun h0 z h1 -> h0 == h1 /\ B.live h1 b /\
                           le_to_n (B.as_seq h1 b) == UInt16.v z))
=
  load16_le_i b 0ul


let store16_be
  (b:B.buffer UInt8.t{B.length b == 2})
  (z:UInt16.t):
  Stack unit
    (requires (fun h -> B.live h b))
    (ensures  (fun h0 _ h1 -> B.(modifies (loc_buffer b) h0 h1) /\ B.live h1 b /\
                           be_to_n (B.as_seq h1 b) == UInt16.v z))
=
  store16_be_i b 0ul z

let load16_be
  (b:B.buffer UInt8.t{B.length b == 2}):
  Stack UInt16.t
    (requires (fun h -> B.live h b))
    (ensures  (fun h0 z h1 -> h0 == h1 /\ B.live h1 b /\
                           be_to_n (B.as_seq h1 b) == UInt16.v z))
=
  load16_be_i b 0ul


let store32_le
  (b:B.buffer UInt8.t{B.length b == 4})
  (z:UInt32.t):
  Stack unit
    (requires (fun h -> B.live h b))
    (ensures  (fun h0 _ h1 -> B.(modifies (loc_buffer b) h0 h1) /\ B.live h1 b /\
                           le_to_n (B.as_seq h1 b) == UInt32.v z))
=
  store32_le_i b 0ul z

let load32_le
  (b:B.buffer UInt8.t{B.length b == 4}):
  Stack UInt32.t
    (requires (fun h -> B.live h b))
    (ensures  (fun h0 z h1 -> h0 == h1 /\ B.live h1 b /\
                           le_to_n (B.as_seq h1 b) == UInt32.v z))
=
  load32_le_i b 0ul


let store32_be
  (b:B.buffer UInt8.t{B.length b == 4})
  (z:UInt32.t):
  Stack unit
    (requires (fun h -> B.live h b))
    (ensures  (fun h0 _ h1 -> B.(modifies (loc_buffer b) h0 h1) /\ B.live h1 b /\
                           be_to_n (B.as_seq h1 b) == UInt32.v z))
=
  store32_be_i b 0ul z

let load32_be
  (b:B.buffer UInt8.t{B.length b == 4}):
  Stack UInt32.t
    (requires (fun h -> B.live h b))
    (ensures  (fun h0 z h1 -> h0 == h1 /\ B.live h1 b /\
                           be_to_n (B.as_seq h1 b) == UInt32.v z))
=
  load32_be_i b 0ul


let store64_le
  (b:B.buffer UInt8.t{B.length b == 8})
  (z:UInt64.t):
  Stack unit
    (requires (fun h -> B.live h b))
    (ensures  (fun h0 _ h1 -> B.(modifies (loc_buffer b) h0 h1) /\ B.live h1 b /\
                           le_to_n (B.as_seq h1 b) == UInt64.v z))
=
  store64_le_i b 0ul z

let load64_le
  (b:B.buffer UInt8.t{B.length b == 8}):
  Stack UInt64.t
    (requires (fun h -> B.live h b))
    (ensures  (fun h0 z h1 -> h0 == h1 /\ B.live h1 b /\
                           le_to_n (B.as_seq h1 b) == UInt64.v z))
=
  load64_le_i b 0ul


let load64_be
  (b:B.buffer UInt8.t{B.length b == 8}):
  Stack UInt64.t
    (requires (fun h -> B.live h b))
    (ensures  (fun h0 z h1 -> h0 == h1 /\ B.live h1 b /\
                           be_to_n (B.as_seq h1 b) == UInt64.v z))
=
  load64_be_i b 0ul

let store64_be
  (b:B.buffer UInt8.t{B.length b == 8})
  (z:UInt64.t):
  Stack unit
    (requires (fun h -> B.live h b))
    (ensures  (fun h0 _ h1 -> B.(modifies (loc_buffer b) h0 h1) /\ B.live h1 b /\
                           be_to_n (B.as_seq h1 b) == UInt64.v z))
=
  store64_be_i b 0ul z


let load128_le
  (b:B.buffer UInt8.t{B.length b == 16}):
  Stack UInt128.t
    (requires (fun h -> B.live h b))
    (ensures  (fun h0 z h1 -> h0 == h1 /\ B.live h1 b /\
                           le_to_n (B.as_seq h1 b) == UInt128.v z))
=
  load128_le_i b 0ul

let store128_le
  (b:B.buffer UInt8.t{B.length b == 16})
  (z:UInt128.t):
  Stack unit
    (requires (fun h -> B.live h b))
    (ensures  (fun h0 _ h1 -> B.(modifies (loc_buffer b) h0 h1) /\ B.live h1 b /\
                           le_to_n (B.as_seq h1 b) == UInt128.v z))
=
  store128_le_i b 0ul z


let load128_be
  (b:B.buffer UInt8.t{B.length b == 16}):
  Stack UInt128.t
    (requires (fun h -> B.live h b))
    (ensures  (fun h0 z h1 -> h0 == h1 /\ B.live h1 b /\
                           be_to_n (B.as_seq h1 b) == UInt128.v z))
=
  load128_be_i b 0ul

let store128_be
  (b:B.buffer UInt8.t{B.length b = 16})
  (z:UInt128.t):
  Stack unit
    (requires (fun h -> B.live h b))
    (ensures  (fun h0 _ h1 -> B.(modifies (loc_buffer b) h0 h1) /\ B.live h1 b /\
                           be_to_n (B.as_seq h1 b) == UInt128.v z))
=
  store128_be_i b 0ul z

/// Index and update
/// ----------------
///
/// These are more sophisticated than load/store above, because they reason
/// over the underlying sequence of bytes interpreted as a sequence of (little|big)-endian
/// integers.

#set-options "--z3rlimit 20 --max_fuel 0 --max_ifuel 0"

inline_for_extraction
let index_32_be
  (#rrel #rel:MB.srel u8) (b:MB.mbuffer u8 rrel rel)
  (i:u32)
  : Stack u32
      (requires fun h ->
        MB.live h b /\ MB.length b % 4 = 0 /\
        U32.v i < MB.length b / 4)
      (ensures fun h0 r h1 ->
        h0 == h1 /\
        r = Seq.index (seq_uint32_of_be (MB.length b / 4) (MB.as_seq h0 b)) (U32.v i))
  = load32_be_i b FStar.UInt32.(4ul *^ i)

inline_for_extraction
let index_32_le
  (#rrel #rel:MB.srel u8) (b:MB.mbuffer u8 rrel rel)
  (i:u32)
  : Stack u32
      (requires fun h ->
        MB.live h b /\ MB.length b % 4 = 0 /\
        U32.v i < MB.length b / 4)
      (ensures fun h0 r h1 ->
        h0 == h1 /\
        r = Seq.index (seq_uint32_of_le (MB.length b / 4) (MB.as_seq h0 b)) (U32.v i))
  = load32_le_i b FStar.UInt32.(4ul *^ i)

inline_for_extraction
let index_64_be
  (#rrel #rel:MB.srel u8) (b:MB.mbuffer u8 rrel rel)
  (i:u32)
  : Stack u64
      (requires fun h ->
        MB.live h b /\ MB.length b % 8 = 0 /\
        U32.v i < MB.length b / 8)
      (ensures fun h0 r h1 ->
        h0 == h1 /\
        r = Seq.index (seq_uint64_of_be (MB.length b / 8) (MB.as_seq h0 b)) (UInt32.v i))
  = load64_be_i b FStar.UInt32.(8ul *^ i)

inline_for_extraction
let index_64_le
  (#rrel #rel:MB.srel u8) (b:MB.mbuffer u8 rrel rel)
  (i:u32)
  : Stack u64
      (requires fun h ->
        MB.live h b /\ MB.length b % 8 = 0 /\
        U32.v i < MB.length b / 8)
      (ensures fun h0 r h1 ->
        h0 == h1 /\
        r = Seq.index (seq_uint64_of_le (MB.length b / 8) (MB.as_seq h0 b)) (UInt32.v i))
  = load64_le_i b FStar.UInt32.(8ul *^ i)

#reset-options "--using_facts_from 'Prims'"

let interval_4_disjoint (i j: nat)
  : Lemma
    (requires (i <> j))
    (ensures  (let open FStar.Mul in 4 * i + 4 <= 4 * j \/ 4 * j + 4 <= 4 * i))
  = ()

#reset-options "--z3rlimit 16 --max_fuel 0 --max_ifuel 0"

open FStar.Mul

inline_for_extraction
let upd_32_be
  (#rrel #rel:MB.srel u8) (b:MB.mbuffer u8 rrel rel)
  (i:u32) (v:u32)
  : Stack unit
     (requires fun h ->
       MB.length b % 4 = 0 /\
       U32.v i < MB.length b / 4 /\
       store_pre b (U32.(v (4ul *^ i))) 4 (fun s -> be_to_n s == U32.v v) h)
     (ensures fun h0 _ h1 ->
       MB.(modifies (loc_buffer b) h0 h1) /\
       seq_uint32_of_be (MB.length b / 4) (MB.as_seq h1 b) `Seq.equal` Seq.upd (seq_uint32_of_be (MB.length b / 4) (MB.as_seq h0 b)) (U32.v i) v)
  = let h0 = get () in
    store32_be_i b U32.(4ul *^ i) v;
    let h1 = get () in
    //AR: 03/01: the following 3 assertions say how the buffer changed
    assert (be_to_n (Seq.slice (MB.as_seq h1 b) (U32.(v (4ul *^ i))) (U32.(v (4ul *^ i) + 4))) == U32.v v);
    assert (Seq.equal (Seq.slice (MB.as_seq h0 b) 0 (U32.(v (4ul *^ i))))
                      (Seq.slice (MB.as_seq h1 b) 0 (U32.(v (4ul *^ i)))));
    assert (Seq.equal (Seq.slice (MB.as_seq h0 b) (U32.(v (4ul *^ i) + 4)) (MB.length b))
                      (Seq.slice (MB.as_seq h1 b) (U32.(v (4ul *^ i) + 4)) (MB.length b)));
    let f () : Lemma
      (seq_uint32_of_be (MB.length b / 4) (MB.as_seq h1 b) `Seq.equal` Seq.upd (seq_uint32_of_be (MB.length b / 4) (MB.as_seq h0 b))
                        (UInt32.v i) v)
    = let s0 = MB.as_seq h0 b in
      let s1 = MB.as_seq h1 b in
      let n = MB.length b / 4 in
      assert (4 `Prims.op_Multiply` n == MB.length b);
      let s0' = seq_uint32_of_be n s0 in
      let s1' = seq_uint32_of_be n s1 in
      let lo = UInt32.v i in
      let hi = lo + 1 in
      let s2' = Seq.upd s0' lo v in
      assert (Seq.length s1' == Seq.length s2');
      let i' = UInt32.v i in
      let g
        (j' : nat)
      : Lemma
        (requires (j' < n))
        (ensures (j' < n /\ Seq.index s1' j' == Seq.index s2' j'))
      = if j' = UInt32.v i
        then ()
        else begin
          let u () : Lemma
            (Seq.slice s0 (4 * j') (4 * j' + 4) == Seq.slice s1 (4 * j') (4 * j' + 4))
          = if j' < UInt32.v i
            then begin
              Seq.slice_slice s0 0 (4 * i') (4 * j') (4 * j' + 4);
              Seq.slice_slice s1 0 (4 * i') (4 * j') (4 * j' + 4)
            end else begin
              Seq.slice_slice s0 (4 * i' + 4) (MB.length b) (4 * (j' - i' - 1)) (4 * (j' - i'));
              Seq.slice_slice s1 (4 * i' + 4) (MB.length b) (4 * (j' - i' - 1)) (4 * (j' - i'))
            end
          in
          u ()
        end
      in
      Classical.forall_intro (Classical.move_requires g)
    in
    f ()
