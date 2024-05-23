module Lib.IntTypes

open FStar.Mul

#push-options "--max_fuel 0 --max_ifuel 1 --z3rlimit 20"

// Other instances frollow from `FStar.UInt.pow2_values` which is in
// scope of every module depending on Lib.IntTypes
val pow2_2: n:nat -> Lemma (pow2 2 = 4)  [SMTPat (pow2 n)]
val pow2_3: n:nat -> Lemma (pow2 3 = 8)  [SMTPat (pow2 n)]
val pow2_4: n:nat -> Lemma (pow2 4 = 16) [SMTPat (pow2 n)]
val pow2_127: n:nat -> Lemma (pow2 127 = 0x80000000000000000000000000000000) [SMTPat (pow2 n)]

///
/// Definition of machine integer base types
///

type inttype =
  | U1 | U8 | U16 | U32 | U64 | U128 | S8 | S16 | S32 | S64 | S128

[@(strict_on_arguments [0])]
unfold
inline_for_extraction
let unsigned = function
  | U1 | U8 | U16 | U32 | U64 | U128 -> true
  | _ -> false

[@(strict_on_arguments [0])]
unfold
inline_for_extraction
let signed = function
  | S8 | S16 | S32 | S64 | S128 -> true
  | _ -> false

///
/// Operations on the underlying machine integer base types
///

[@(strict_on_arguments [0])]
unfold
inline_for_extraction
let numbytes = function
  | U1   -> 1
  | U8   -> 1
  | S8   -> 1
  | U16  -> 2
  | S16  -> 2
  | U32  -> 4
  | S32  -> 4
  | U64  -> 8
  | S64  -> 8
  | U128 -> 16
  | S128 -> 16

[@(strict_on_arguments [0])]
unfold
inline_for_extraction
let bits = function
  | U1   -> 1
  | U8   -> 8
  | S8   -> 8
  | U16  -> 16
  | S16  -> 16
  | U32  -> 32
  | S32  -> 32
  | U64  -> 64
  | S64  -> 64
  | U128 -> 128
  | S128 -> 128

val bits_numbytes: t:inttype{~(U1? t)} -> Lemma (bits t == 8 * numbytes t)
//  [SMTPat [bits t; numbytes t]]

unfold
let modulus (t:inttype) = pow2 (bits t)

[@(strict_on_arguments [0])]
unfold
let maxint (t:inttype) =
  if unsigned t then pow2 (bits t) - 1 else pow2 (bits t - 1) - 1

[@(strict_on_arguments [0])]
unfold
let minint (t:inttype) =
  if unsigned t then 0 else -(pow2 (bits t - 1))

let range (n:int) (t:inttype) : Type0 =
  minint t <= n /\ n <= maxint t

unfold
type range_t (t:inttype) = x:int{range x t}

///
/// PUBLIC Machine Integers
///

inline_for_extraction
let pub_int_t = function
  | U1   -> n:UInt8.t{UInt8.v n < 2}
  | U8   -> UInt8.t
  | U16  -> UInt16.t
  | U32  -> UInt32.t
  | U64  -> UInt64.t
  | U128 -> UInt128.t
  | S8   -> Int8.t
  | S16  -> Int16.t
  | S32  -> Int32.t
  | S64  -> Int64.t
  | S128 -> Int128.t


[@(strict_on_arguments [0])]
unfold
let pub_int_v #t (x:pub_int_t t) : range_t t =
  match t with
  | U1   -> UInt8.v x
  | U8   -> UInt8.v x
  | U16  -> UInt16.v x
  | U32  -> UInt32.v x
  | U64  -> UInt64.v x
  | U128 -> UInt128.v x
  | S8   -> Int8.v x
  | S16  -> Int16.v x
  | S32  -> Int32.v x
  | S64  -> Int64.v x
  | S128 -> Int128.v x

///
/// SECRET Machine Integers
///

type secrecy_level =
  | SEC
  | PUB

inline_for_extraction
val sec_int_t: inttype -> Type0

val sec_int_v: #t:inttype -> sec_int_t t -> range_t t

///
/// GENERIC Machine Integers
///

inline_for_extraction
let int_t (t:inttype) (l:secrecy_level) =
  match l with
  | PUB -> pub_int_t t
  | SEC -> sec_int_t t

[@(strict_on_arguments [1])]
let v #t #l (u:int_t t l) : range_t t =
  match l with
  | PUB -> pub_int_v #t u
  | SEC -> sec_int_v #t u

unfold
let uint_t (t:inttype{unsigned t}) (l:secrecy_level) = int_t t l

unfold
let sint_t (t:inttype{signed t}) (l:secrecy_level) = int_t t l

unfold
let uint_v #t #l (u:uint_t t l) = v u

unfold
let sint_v #t #l (u:sint_t t l) = v u

unfold
type uint1 = uint_t U1 SEC

unfold
type uint8 = uint_t U8 SEC

unfold
type int8 = sint_t S8 SEC

unfold
type uint16 = uint_t U16 SEC

unfold
type int16 = sint_t S16 SEC

unfold
type uint32 = uint_t U32 SEC

unfold
type int32 = sint_t S32 SEC

unfold
type uint64 = uint_t U64 SEC

unfold
type int64 = sint_t S64 SEC

unfold
type uint128 = uint_t U128 SEC

unfold
type int128 = sint_t S128 SEC

unfold
type bit_t = uint_t U1 PUB

unfold
type byte_t = uint_t U8 PUB

unfold
type size_t = uint_t U32 PUB

// 2019.7.19: Used only by experimental Blake2b; remove?
unfold
type size128_t = uint_t U128 PUB

unfold
type pub_uint8 = uint_t U8 PUB

unfold
type pub_int8 = sint_t S8 PUB

unfold
type pub_uint16 = uint_t U16 PUB

unfold
type pub_int16 = sint_t S16 PUB

unfold
type pub_uint32 = uint_t U32 PUB

unfold
type pub_int32 = sint_t S32 PUB

unfold
type pub_uint64 = uint_t U64 PUB

unfold
type pub_int64 = sint_t S64 PUB

unfold
type pub_uint128 = uint_t U128 PUB

unfold
type pub_int128 = sint_t S128 PUB

///
/// Casts between mathematical and machine integers
///

inline_for_extraction
val secret: #t:inttype -> x:int_t t PUB -> y:int_t t SEC{v x == v y}

[@(strict_on_arguments [0])]
inline_for_extraction
val mk_int: #t:inttype -> #l:secrecy_level -> n:range_t t -> u:int_t t l{v u == n}

unfold
let uint (#t:inttype{unsigned t}) (#l:secrecy_level) (n:range_t t) = mk_int #t #l n

unfold
let sint (#t:inttype{signed t}) (#l:secrecy_level) (n:range_t t) = mk_int #t #l n

val v_injective: #t:inttype -> #l:secrecy_level -> a:int_t t l -> Lemma
  (mk_int (v #t #l a) == a)
  [SMTPat (v #t #l a)]

val v_mk_int: #t:inttype -> #l:secrecy_level -> n:range_t t -> Lemma
  (v #t #l (mk_int #t #l n) == n)
  [SMTPat (v #t #l (mk_int #t #l n))]

unfold
let u1 (n:range_t U1) : u:uint1{v u == n} = uint #U1 #SEC n

unfold
let u8 (n:range_t U8) : u:uint8{v u == n} = uint #U8 #SEC n

unfold
let i8 (n:range_t S8) : u:int8{v u == n} = sint #S8 #SEC n

unfold
let u16 (n:range_t U16) : u:uint16{v u == n} = uint #U16 #SEC n

unfold
let i16 (n:range_t S16) : u:int16{v u == n} = sint #S16 #SEC n

unfold
let u32 (n:range_t U32) : u:uint32{v u == n} = uint #U32 #SEC n

unfold
let i32 (n:range_t S32) : u:int32{v u == n} = sint #S32 #SEC n

unfold
let u64 (n:range_t U64) : u:uint64{v u == n} = uint #U64 #SEC n

unfold
let i64 (n:range_t S64) : u:int64{v u == n} = sint #S64 #SEC n

(* We only support 64-bit literals, hence the unexpected upper limit *)
inline_for_extraction
val u128: n:range_t U64 -> u:uint128{v #U128 u == n}

inline_for_extraction
val i128 (n:range_t S64) : u:int128{v #S128 u == n}

unfold
let max_size_t = maxint U32

unfold
type size_nat = n:nat{n <= max_size_t}

unfold
type size_pos = n:pos{n <= max_size_t}

unfold
let size (n:size_nat) : size_t = uint #U32 #PUB n

unfold
let size_v (s:size_t) = v s

unfold
let byte (n:nat{n < 256}) : b:byte_t{v b == n} = uint #U8 #PUB n

unfold
let byte_v (s:byte_t) : n:size_nat{v s == n} = v s

inline_for_extraction
val size_to_uint32: s:size_t -> u:uint32{u == u32 (v s)}

inline_for_extraction
val size_to_uint64: s:size_t -> u:uint64{u == u64 (v s)}

inline_for_extraction
val byte_to_uint8: s:byte_t -> u:uint8{u == u8 (v s)}

[@(strict_on_arguments [0])]
inline_for_extraction
let op_At_Percent_Dot x t =
  if unsigned t then x % modulus t
  else FStar.Int.(x @% modulus t)

// Casting a value to a signed type is implementation-defined when the value can't
// be represented in the new type; e.g. (int8_t)128UL is implementation-defined
// We rule out this case in the type of `u1`
// See 6.3.1.3 in http://www.open-std.org/jtc1/sc22/wg14/www/docs/n1548.pdf
[@(strict_on_arguments [0;2])]
inline_for_extraction
val cast: #t:inttype -> #l:secrecy_level
  -> t':inttype
  -> l':secrecy_level{PUB? l \/ SEC? l'}
  -> u1:int_t t l{unsigned t' \/ range (v u1) t'}
  -> u2:int_t t' l'{v u2 == v u1 @%. t'}

[@(strict_on_arguments [0])]
unfold
let to_u1 #t #l u : uint1 = cast #t #l U1 SEC u

[@(strict_on_arguments [0])]
unfold
let to_u8 #t #l u : uint8 = cast #t #l U8 SEC u

[@(strict_on_arguments [0])]
unfold
let to_i8 #t #l u : int8 = cast #t #l S8 SEC u

[@(strict_on_arguments [0])]
unfold
let to_u16 #t #l u : uint16 = cast #t #l U16 SEC u

[@(strict_on_arguments [0])]
unfold
let to_i16 #t #l u : int16 = cast #t #l S16 SEC u

[@(strict_on_arguments [0])]
unfold
let to_u32 #t #l u : uint32 = cast #t #l U32 SEC u

[@(strict_on_arguments [0])]
unfold
let to_i32 #t #l u : int32 = cast #t #l S32 SEC u

[@(strict_on_arguments [0])]
unfold
let to_u64 #t #l u : uint64 = cast #t #l U64 SEC u

[@(strict_on_arguments [0])]
unfold
let to_i64 #t #l u : int64 = cast #t #l S64 SEC u

[@(strict_on_arguments [0])]
unfold
let to_u128 #t #l u : uint128 = cast #t #l U128 SEC u

[@(strict_on_arguments [0])]
unfold
let to_i128 #t #l u : int128 = cast #t #l S128 SEC u

///
/// Bitwise operators for all machine integers
///

[@(strict_on_arguments [0])]
inline_for_extraction
let ones_v (t:inttype) =
  match t with
  | U1 | U8 | U16 | U32 | U64 | U128 -> maxint t
  | S8 | S16 | S32 | S64 | S128 -> -1

[@(strict_on_arguments [0])]
inline_for_extraction
val ones: t:inttype -> l:secrecy_level -> n:int_t t l{v n = ones_v t}

inline_for_extraction
val zeros: t:inttype -> l:secrecy_level -> n:int_t t l{v n = 0}

[@(strict_on_arguments [0])]
inline_for_extraction
val add_mod: #t:inttype{unsigned t} -> #l:secrecy_level
  -> int_t t l
  -> int_t t l
  -> int_t t l

val add_mod_lemma: #t:inttype{unsigned t} -> #l:secrecy_level
  -> a:int_t t l
  -> b:int_t t l
  -> Lemma
    (v (add_mod a b) == (v a + v b) @%. t)
    [SMTPat (v #t #l (add_mod #t #l a b))]

[@(strict_on_arguments [0])]
inline_for_extraction
val add: #t:inttype -> #l:secrecy_level
  -> a:int_t t l
  -> b:int_t t l{range (v a + v b) t}
  -> int_t t l

val add_lemma: #t:inttype -> #l:secrecy_level
  -> a:int_t t l
  -> b:int_t t l{range (v a + v b) t}
  -> Lemma
    (v #t #l (add #t #l a b) == v a + v b)
    [SMTPat (v #t #l (add #t #l a b))]

[@(strict_on_arguments [0])]
inline_for_extraction
val incr: #t:inttype -> #l:secrecy_level
  -> a:int_t t l{v a < maxint t}
  -> int_t t l

val incr_lemma: #t:inttype -> #l:secrecy_level
  -> a:int_t t l{v a < maxint t}
  -> Lemma (v (incr a) == v a + 1)

[@(strict_on_arguments [0])]
inline_for_extraction
val mul_mod: #t:inttype{unsigned t /\ ~(U128? t)} -> #l:secrecy_level
  -> int_t t l
  -> int_t t l
  -> int_t t l

val mul_mod_lemma: #t:inttype{unsigned t /\ ~(U128? t)} -> #l:secrecy_level
  -> a:int_t t l
  -> b:int_t t l
  -> Lemma (v (mul_mod a b) == (v a * v b) @%. t)
  [SMTPat (v #t #l (mul_mod #t #l a b))]

[@(strict_on_arguments [0])]
inline_for_extraction
val mul: #t:inttype{~(U128? t) /\ ~(S128? t)} -> #l:secrecy_level
  -> a:int_t t l
  -> b:int_t t l{range (v a * v b) t}
  -> int_t t l

val mul_lemma: #t:inttype{~(U128? t) /\ ~(S128? t)} -> #l:secrecy_level
  -> a:int_t t l
  -> b:int_t t l{range (v a * v b) t}
  -> Lemma (v #t #l (mul #t #l a b) == v a * v b)
  [SMTPat (v #t #l (mul #t #l a b))]

inline_for_extraction
val mul64_wide: uint64 -> uint64 -> uint128

val mul64_wide_lemma: a:uint64 -> b:uint64 -> Lemma
  (v (mul64_wide a b) == v a * v b)
  [SMTPat (v (mul64_wide a b))]
// KB: I'd prefer
// v (mul64_wide a b) = (pow2 (bits t) + v a - v b) % pow2 (bits t)

inline_for_extraction
val mul_s64_wide: int64 -> int64 -> int128

val mul_s64_wide_lemma: a:int64 -> b:int64 -> Lemma
  (v (mul_s64_wide a b) == v a * v b)
  [SMTPat (v (mul_s64_wide a b))]

[@(strict_on_arguments [0])]
inline_for_extraction
val sub_mod: #t:inttype{unsigned t} -> #l:secrecy_level
  -> int_t t l
  -> int_t t l
  -> int_t t l

val sub_mod_lemma: #t:inttype{unsigned t} -> #l:secrecy_level -> a:int_t t l -> b:int_t t l
  -> Lemma (v (sub_mod a b) == (v a - v b) @%. t)
  [SMTPat (v #t #l (sub_mod #t #l a b))]

[@(strict_on_arguments [0])]
inline_for_extraction
val sub: #t:inttype -> #l:secrecy_level
  -> a:int_t t l
  -> b:int_t t l{range (v a - v b) t}
  -> int_t t l

val sub_lemma: #t:inttype -> #l:secrecy_level
  -> a:int_t t l
  -> b:int_t t l{range (v a - v b) t}
  -> Lemma (v (sub a b) == v a - v b)
    [SMTPat (v #t #l (sub #t #l a b))]

[@(strict_on_arguments [0])]
inline_for_extraction
val decr: #t:inttype -> #l:secrecy_level
  -> a:int_t t l{minint t < v a}
  -> int_t t l

val decr_lemma: #t:inttype -> #l:secrecy_level
  -> a:int_t t l{minint t < v a}
  -> Lemma (v (decr a) == v a - 1)

[@(strict_on_arguments [0])]
inline_for_extraction
val logxor: #t:inttype -> #l:secrecy_level
  -> int_t t l
  -> int_t t l
  -> int_t t l

val logxor_lemma: #t:inttype -> #l:secrecy_level -> a:int_t t l -> b:int_t t l -> Lemma
  (a `logxor` (a `logxor` b) == b /\
   a `logxor` (b `logxor` a) == b /\
   a `logxor` (mk_int #t #l 0) == a)

val logxor_lemma1: #t:inttype -> #l:secrecy_level -> a:int_t t l -> b:int_t t l -> Lemma
  (requires range (v a) U1 /\ range (v b) U1)
  (ensures  range (v (a `logxor` b)) U1)

let logxor_v (#t:inttype) (a:range_t t) (b:range_t t) : range_t t =
  match t with
  | S8 | S16 | S32 | S64 | S128 -> Int.logxor #(bits t) a b
  | _ -> UInt.logxor #(bits t) a b

val logxor_spec: #t:inttype -> #l:secrecy_level
  -> a:int_t t l
  -> b:int_t t l
  -> Lemma (v (a `logxor` b) == v a `logxor_v` v b)

[@(strict_on_arguments [0])]
inline_for_extraction
val logand: #t:inttype -> #l:secrecy_level
  -> int_t t l
  -> int_t t l
  -> int_t t l

val logand_zeros: #t:inttype -> #l:secrecy_level -> a:int_t t l ->
  Lemma (v (a `logand` zeros t l) == 0)

val logand_ones: #t:inttype -> #l:secrecy_level -> a:int_t t l ->
  Lemma (v (a `logand` ones t l) == v a)

// For backwards compatibility
val logand_lemma: #t:inttype -> #l:secrecy_level
  -> a:int_t t l
  -> b:int_t t l
  -> Lemma
    (requires v a = 0 \/ v a = ones_v t)
    (ensures  (if v a = 0 then v (a `logand` b) == 0 else v (a `logand` b) == v b))

let logand_v (#t:inttype) (a:range_t t) (b:range_t t) : range_t t =
  match t with
  | S8 | S16 | S32 | S64 | S128 -> Int.logand #(bits t) a b
  | _ -> UInt.logand #(bits t) a b

val logand_spec: #t:inttype -> #l:secrecy_level
  -> a:int_t t l
  -> b:int_t t l
  -> Lemma (v (a `logand` b) == v a `logand_v` v b)
  //[SMTPat (v (a `logand` b))]

val logand_le:#t:inttype{unsigned t} -> #l:secrecy_level -> a:uint_t t l -> b:uint_t t l ->
  Lemma (requires True)
        (ensures v (logand a b) <= v a /\ v (logand a b) <= v b)

val logand_mask: #t:inttype{unsigned t} -> #l:secrecy_level -> a:uint_t t l -> b:uint_t t l ->   m:pos{m < bits t} ->
  Lemma
    (requires v b == pow2 m - 1)
    (ensures v (logand #t #l a b) == v a % pow2 m)

[@(strict_on_arguments [0])]
inline_for_extraction
val logor: #t:inttype -> #l:secrecy_level
  -> int_t t l
  -> int_t t l
  -> int_t t l

val logor_disjoint: #t:inttype{unsigned t} -> #l:secrecy_level
  -> a:int_t t l
  -> b:int_t t l
  -> m:nat{m < bits t}
  -> Lemma
    (requires 0 <= v a /\ v a < pow2 m /\ v b % pow2 m == 0)
    (ensures  v (a `logor` b) == v a + v b)
  //[SMTPat (v (a `logor` b))]

val logor_zeros: #t: inttype -> #l: secrecy_level -> a: int_t t l ->
  Lemma (v (a `logor` zeros t l) == v a)

val logor_ones: #t: inttype -> #l: secrecy_level -> a: int_t t l ->
  Lemma (v (a `logor` ones t l) == ones_v t)

// For backwards compatibility
val logor_lemma: #t:inttype -> #l:secrecy_level
  -> a:int_t t l
  -> b:int_t t l
  -> Lemma
    (requires v a = 0 \/ v a = ones_v t)
    (ensures  (if v a = ones_v t then v (a `logor` b) == ones_v t else v (a `logor` b) == v b))

let logor_v (#t:inttype) (a:range_t t) (b:range_t t) : range_t t =
  match t with
  | S8 | S16 | S32 | S64 | S128 -> Int.logor #(bits t) a b
  | _ -> UInt.logor #(bits t) a b

val logor_spec: #t:inttype -> #l:secrecy_level
  -> a:int_t t l
  -> b:int_t t l
  -> Lemma (v (a `logor` b) == v a `logor_v` v b)


[@(strict_on_arguments [0])]
inline_for_extraction
val lognot: #t:inttype -> #l:secrecy_level -> int_t t l -> int_t t l

val lognot_lemma: #t: inttype -> #l: secrecy_level ->
  a: int_t t l ->
  Lemma
    (requires v a = 0 \/ v a = ones_v t)
    (ensures (if v a = ones_v t then v (lognot a) == 0 else v (lognot a) == ones_v t))

let lognot_v (#t:inttype) (a:range_t t) : range_t t =
  match t with
  | S8 | S16 | S32 | S64 | S128 -> Int.lognot #(bits t) a
  | _ -> UInt.lognot #(bits t) a

val lognot_spec: #t:inttype -> #l:secrecy_level
  -> a:int_t t l
  -> Lemma (v (lognot a) == lognot_v (v a))

inline_for_extraction
type shiftval (t:inttype) = u:size_t{v u < bits t}

inline_for_extraction
type rotval (t:inttype) = u:size_t{0 < v u /\ v u < bits t}

[@(strict_on_arguments [0])]
inline_for_extraction
val shift_right: #t:inttype -> #l:secrecy_level
  -> int_t t l
  -> shiftval t
  -> int_t t l

val shift_right_lemma: #t:inttype -> #l:secrecy_level
  -> a:int_t t l
  -> b:shiftval t
  -> Lemma
    (v (shift_right a b) == v a / pow2 (v b))
    [SMTPat (v #t #l (shift_right #t #l a b))]

[@(strict_on_arguments [0])]
inline_for_extraction
val shift_left: #t:inttype -> #l:secrecy_level
  -> a:int_t t l
  -> s:shiftval t
  -> Pure (int_t t l)
    (requires unsigned t \/ (0 <= v a /\ v a * pow2 (v s) <= maxint t))
    (ensures  fun _ -> True)

val shift_left_lemma:
    #t:inttype
  -> #l:secrecy_level
  -> a:int_t t l{unsigned t \/ 0 <= v a}
  -> s:shiftval t{unsigned t \/ (0 <= v a /\ v a * pow2 (v s) <= maxint t)}
  -> Lemma
    (v (shift_left a s) == (v a * pow2 (v s)) @%. t)
    [SMTPat (v #t #l (shift_left #t #l a s))]

[@(strict_on_arguments [0])]
inline_for_extraction
val rotate_right: #t:inttype -> #l:secrecy_level
  -> a:int_t t l{unsigned t}
  -> rotval t
  -> int_t t l

[@(strict_on_arguments [0])]
inline_for_extraction
val rotate_left: #t:inttype -> #l:secrecy_level
  -> a:int_t t l{unsigned t}
  -> rotval t
  -> int_t t l

inline_for_extraction
let shift_right_i (#t:inttype) (#l:secrecy_level) (s:shiftval t{unsigned t}) (u:uint_t t l) : uint_t t l = shift_right u s

inline_for_extraction
let shift_left_i (#t:inttype) (#l:secrecy_level) (s:shiftval t{unsigned t}) (u:uint_t t l) : uint_t t l = shift_left u s

inline_for_extraction
let rotate_right_i (#t:inttype) (#l:secrecy_level) (s:rotval t{unsigned t}) (u:uint_t t l) : uint_t t l = rotate_right u s

inline_for_extraction
let rotate_left_i (#t:inttype) (#l:secrecy_level) (s:rotval t{unsigned t}) (u:uint_t t l) : uint_t t l = rotate_left u s


[@(strict_on_arguments [0])]
inline_for_extraction
val ct_abs: #t:inttype{signed t /\ ~(S128? t)} -> #l:secrecy_level
  -> a:int_t t l{minint t < v a}
  -> b:int_t t l{v b == abs (v a)}

///
/// Masking operators for all machine integers
///

[@(strict_on_arguments [0])]
inline_for_extraction
val eq_mask: #t:inttype{~(S128? t)} -> int_t t SEC -> int_t t SEC -> int_t t SEC

val eq_mask_lemma: #t:inttype{~(S128? t)} -> a:int_t t SEC -> b:int_t t SEC -> Lemma
  (if v a = v b then v (eq_mask a b) == ones_v t
                else v (eq_mask a b) == 0)
  [SMTPat (eq_mask #t a b)]

val eq_mask_logand_lemma:
    #t:inttype{~(S128? t)}
  -> a:int_t t SEC
  -> b:int_t t SEC
  -> c:int_t t SEC -> Lemma
  (if v a = v b then v (c `logand` eq_mask a b) == v c
                else v (c `logand` eq_mask a b) == 0)
  [SMTPat (c `logand` eq_mask a b)]

[@(strict_on_arguments [0])]
inline_for_extraction
val neq_mask: #t:inttype{~(S128? t)} -> a:int_t t SEC -> b:int_t t SEC -> int_t t SEC

val neq_mask_lemma: #t:inttype{~(S128? t)} -> a:int_t t SEC -> b:int_t t SEC -> Lemma
  (if v a = v b then v (neq_mask a b) == 0
                else v (neq_mask a b) == ones_v t)
  [SMTPat (neq_mask #t a b)]

[@(strict_on_arguments [0])]
inline_for_extraction
val gte_mask: #t:inttype{unsigned t} -> int_t t SEC -> b:int_t t SEC -> int_t t SEC

val gte_mask_lemma: #t:inttype{unsigned t} -> a:int_t t SEC -> b:int_t t SEC -> Lemma
  (if v a >= v b then v (gte_mask a b) == ones_v t
                else v (gte_mask a b) == 0)
  [SMTPat (gte_mask #t a b)]

val gte_mask_logand_lemma: #t:inttype{unsigned t}
  -> a:int_t t SEC
  -> b:int_t t SEC
  -> c:int_t t SEC
  -> Lemma
  (if v a >= v b then v (c `logand` gte_mask a b) == v c
                else v (c `logand` gte_mask a b) == 0)
  [SMTPat (c `logand` gte_mask a b)]

[@(strict_on_arguments [0])]
inline_for_extraction
val lt_mask: #t:inttype{unsigned t} -> int_t t SEC -> int_t t SEC -> int_t t SEC

val lt_mask_lemma: #t:inttype{unsigned t} -> a:int_t t SEC -> b:int_t t SEC -> Lemma
  (if v a < v b then v (lt_mask a b) == ones_v t
                else v (lt_mask a b) == 0)
  [SMTPat (lt_mask #t a b)]

[@(strict_on_arguments [0])]
inline_for_extraction
val gt_mask: #t:inttype{unsigned t} -> int_t t SEC -> b:int_t t SEC -> int_t t SEC

val gt_mask_lemma: #t:inttype{unsigned t} -> a:int_t t SEC -> b:int_t t SEC -> Lemma
  (if v a > v b then v (gt_mask a b) == ones_v t
                else v (gt_mask a b) == 0)
  [SMTPat (gt_mask #t a b)]

[@(strict_on_arguments [0])]
inline_for_extraction
val lte_mask: #t:inttype{unsigned t} -> int_t t SEC -> int_t t SEC -> int_t t SEC

val lte_mask_lemma: #t:inttype{unsigned t} -> a:int_t t SEC -> b:int_t t SEC -> Lemma
  (if v a <= v b then v (lte_mask a b) == ones_v t
                else v (lte_mask a b) == 0)
  [SMTPat (lte_mask #t a b)]

#push-options "--max_fuel 1"

[@(strict_on_arguments [0])]
inline_for_extraction
let mod_mask (#t:inttype) (#l:secrecy_level) (m:shiftval t{pow2 (uint_v m) <= maxint t}) : int_t t l =
  shift_left_lemma #t #l (mk_int 1) m;
  (mk_int 1 `shift_left` m) `sub` mk_int 1

#pop-options

val mod_mask_lemma: #t:inttype -> #l:secrecy_level
  -> a:int_t t l -> m:shiftval t{pow2 (uint_v m) <= maxint t}
  -> Lemma (v (a `logand` mod_mask m) == v a % pow2 (v m))
  [SMTPat (a `logand` mod_mask #t m)]

(** Casts a value between two signed types using modular reduction *)
[@(strict_on_arguments [0;2])]
inline_for_extraction
val cast_mod: #t:inttype{signed t} -> #l:secrecy_level
  -> t':inttype{signed t'}
  -> l':secrecy_level{PUB? l \/ SEC? l'}
  -> a:int_t t l
  -> b:int_t t' l'{v b == v a @%. t'}

///
/// Operators available for all machine integers
///

unfold
let (+!) #t #l = add #t #l

unfold
let (+.) #t #l = add_mod #t #l

unfold
let ( *! ) #t #l = mul #t #l

unfold
let ( *. ) #t #l = mul_mod #t #l

unfold
let ( -! ) #t #l = sub #t #l

unfold
let ( -. ) #t #l = sub_mod #t #l

unfold
let ( >>. ) #t #l = shift_right #t #l

unfold
let ( <<. ) #t #l = shift_left #t #l

unfold
let ( >>>. ) #t #l = rotate_right #t #l

unfold
let ( <<<. ) #t #l = rotate_left #t #l

unfold
let ( ^. ) #t #l = logxor #t #l

unfold
let ( |. ) #t #l = logor #t #l

unfold
let ( &. ) #t #l = logand #t #l

unfold
let ( ~. ) #t #l = lognot #t #l

///
/// Operations on public integers
///

[@(strict_on_arguments [0])]
inline_for_extraction
val div: #t:inttype{~(U128? t) /\ ~(S128? t)}
  -> a:int_t t PUB
  -> b:int_t t PUB{v b <> 0 /\ (unsigned t \/ range FStar.Int.(v a / v b) t)}
  -> int_t t PUB

val div_lemma: #t:inttype{~(U128? t) /\ ~(S128? t)}
  -> a:int_t t PUB
  -> b:int_t t PUB{v b <> 0 /\ (unsigned t \/ range FStar.Int.(v a / v b) t)}
  -> Lemma (v (div a b) == FStar.Int.(v a / v b))
  [SMTPat (v #t (div #t a b))]

[@(strict_on_arguments [0])]
inline_for_extraction
val mod: #t:inttype{~(U128? t) /\ ~(S128? t)}
  -> a:int_t t PUB
  -> b:int_t t PUB{v b <> 0 /\ (unsigned t \/ range FStar.Int.(v a / v b) t)}
  -> int_t t PUB

val mod_lemma: #t:inttype{~(U128? t) /\ ~(S128? t)}
  -> a:int_t t PUB
  -> b:int_t t PUB{v b <> 0 /\ (unsigned t \/ range FStar.Int.(v a / v b) t)}
  -> Lemma (if signed t then
             v (mod a b) == FStar.Int.mod #(bits t) (v a) (v b)
           else
             v (mod a b) == FStar.UInt.mod #(bits t) (v a) (v b))
  [SMTPat (v #t (mod #t a b))]

[@(strict_on_arguments [0])]
inline_for_extraction
val eq: #t:inttype -> int_t t PUB -> int_t t PUB -> bool

inline_for_extraction
val eq_lemma: #t:inttype
  -> a:int_t t PUB
  -> b:int_t t PUB
  -> Lemma (a `eq` b == (v a = v b))
  [SMTPat (eq #t a b)]

[@(strict_on_arguments [0])]
inline_for_extraction
val ne: #t:inttype -> int_t t PUB -> int_t t PUB -> bool

val ne_lemma: #t:inttype
  -> a:int_t t PUB
  -> b:int_t t PUB
  -> Lemma (a `ne` b == (v a <> v b))
  [SMTPat (ne #t a b)]

[@(strict_on_arguments [0])]
inline_for_extraction
val lt: #t:inttype -> int_t t PUB -> int_t t PUB -> bool

val lt_lemma: #t:inttype
  -> a:int_t t PUB
  -> b:int_t t PUB
  -> Lemma (a `lt` b == (v a < v b))
  [SMTPat (lt #t a b)]

[@(strict_on_arguments [0])]
inline_for_extraction
val lte: #t:inttype -> int_t t PUB -> int_t t PUB -> bool

val lte_lemma: #t:inttype
  -> a:int_t t PUB
  -> b:int_t t PUB
  -> Lemma (a `lte` b == (v a <= v b))
  [SMTPat (lte #t a b)]

[@(strict_on_arguments [0])]
inline_for_extraction
val gt: #t:inttype -> int_t t PUB -> int_t t PUB -> bool

val gt_lemma: #t:inttype
  -> a:int_t t PUB
  -> b:int_t t PUB
  -> Lemma (a `gt` b == (v a > v b))
  [SMTPat (gt #t a b)]

[@(strict_on_arguments [0])]
inline_for_extraction
val gte: #t:inttype -> int_t t PUB -> int_t t PUB -> bool

val gte_lemma: #t:inttype
  -> a:int_t t PUB
  -> b:int_t t PUB
  -> Lemma (a `gte` b == (v a >= v b))
  [SMTPat (gte #t a b)]

unfold
let (/.) #t = div #t

unfold
let (%.) #t = mod #t

unfold
let (=.) #t = eq #t

unfold
let (<>.) #t = ne #t

unfold
let (<.) #t = lt #t

unfold
let (<=.) #t = lte #t

unfold
let (>.) #t = gt #t

unfold
let (>=.) #t = gte #t
