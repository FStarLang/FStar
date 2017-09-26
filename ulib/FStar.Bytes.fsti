module FStar.Bytes

module S = FStar.Seq
module U = FStar.UInt
module U8 = FStar.UInt8
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module Str = FStar.String
module Chr = FStar.Char

unfold let u8 = U8.t
unfold let u16 = U16.t
unfold let u32 = U32.t

(** Realized by uint8_t in C and int in OCaml (char does not have necessary operators...) *)
unfold type byte = u8

val bytes : Type0
val length : bytes -> u32

(**  representation for specs that need lemmas not defined here. *)
val reveal:
    bytes
  -> GTot (S.seq byte)

val length_reveal:
    x:bytes
  -> Lemma (ensures (S.length (reveal x) = UInt32.v (length x)))
          [SMTPatOr [[SMTPat (S.length (reveal x))];
                     [SMTPat (length x)]]]

val hide:
    s:S.seq byte{S.length s < pow2 32}
  -> GTot bytes

val hide_reveal:
    x:bytes
  -> Lemma (ensures (hide (reveal x) == x))
          [SMTPat (reveal x)]

val reveal_hide:
    x:S.seq byte{S.length x < pow2 32}
  -> Lemma (ensures (reveal (hide x) == x))
          [SMTPat (hide x)]

type lbytes (l:nat) = b:bytes{U32.v (length b) = l}
type kbytes (k:nat) = b:bytes{U32.v (length b) < pow2 k}

val empty_bytes : lbytes 0
val empty_unique:
    b:bytes
  -> Lemma (U32.v (length b) = 0 ==> b == empty_bytes)
    [SMTPat (length b)]

(** If you statically know the length, it is OK to read at arbitrary indexes *)
val get:
    b:bytes
  -> pos:nat{pos < U32.v (length b)}
  -> GTot byte

val op_String_Access:
    b:bytes
  -> i:u32{U32.(i <^ length b)}
  -> r:byte{r = get b (U32.v i)}

val extensionality:
    b1:bytes
  -> b2:bytes
  -> Lemma (requires (length b1 = length b2 /\
                     (forall (i:nat{i < U32.v (length b1)}).{:pattern (get b1 i); (get b2 i)} get b1 i == get b2 i)))
          (ensures (b1 == b2))

(** creating byte values **)
val create:
    len:u32
  -> v:byte
  -> b:lbytes (U32.v len){forall (i:u32{U32.(i <^ len)}). b.[i] = v}

val init:
    len:u32
  -> f:(i:u32{U32.(i <^ len)} -> byte)
  -> b:lbytes (U32.v len){forall (i:u32{U32.(i <^ len)}). b.[i] = f i}

let abyte (b:byte) : lbytes 1 =
    create 1ul b

let twobytes (b:byte*byte) : lbytes 2 =
    init 2ul (fun i -> if i = 0ul then fst b else snd b)

(** appending bytes **)
val append:
    b1:bytes
  -> b2:bytes{UInt.size (U32.v (length b1) + U32.v (length b2)) U32.n}
  -> Tot (b:bytes{reveal b == S.append (reveal b1) (reveal b2)})
unfold let op_At_Bar = append

val slice:
    b:bytes
  -> s:u32{U32.(s <=^ length b)}
  -> e:u32{U32.(e <=^ length b /\ s <=^ e)}
  -> r:bytes{reveal r == Seq.slice (reveal b) (U32.v s) (U32.v e)}

val sub:
    b:bytes
  -> s:u32{U32.(s <=^ length b)}
  -> l:u32{U32.v s + U32.v l <= U32.v (length b)}
  -> r:bytes{reveal r == Seq.slice (reveal b) (U32.v s) (U32.v s + U32.v l)}

val split:
    b:bytes
  -> k:u32{U32.v k <= U32.v (length b)}
  -> p:(bytes*bytes){let x, y = p in (reveal x, reveal y) == Seq.split (reveal b) (U32.v k)}

(** Interpret a sequence of bytes as a mathematical integer encoded in big endian **)
type uint_k (k:nat) = U.uint_t (op_Multiply 8 k)

val int_of_bytes:
    b:bytes
  -> GTot (uint_k (U32.v (length b)))

val bytes_of_int:
    #k:nat{k <= 32}
  -> n:uint_k k
  -> lbytes k

val int_of_bytes_of_int:
    #k:nat{k <= 32}
  -> n:uint_k k
  -> Lemma (ensures (int_of_bytes (bytes_of_int n) == n))
          [SMTPat (bytes_of_int n)]

val bytes_of_int_of_bytes:
    b:bytes{U32.v (length b) <= 32}
  -> Lemma (ensures (bytes_of_int (int_of_bytes b) == b))
          [SMTPat (int_of_bytes b)]

val int32_of_bytes:
    b:bytes{U32.v (length b) <= 4}
  -> n:u32{U32.v n == int_of_bytes b}

val int16_of_bytes:
    b:bytes{U32.v (length b) <= 2}
  -> n:u16{U16.v n == int_of_bytes b}

val int8_of_bytes:
    b:bytes{U32.v (length b) = 1}
  -> n:u8{U8.v n = int_of_bytes b}

val bytes_of_int32:
    n:U32.t
  -> b:lbytes 4{b == bytes_of_int #4 (U32.v n)}

val bytes_of_int16:
    n:U16.t
  -> b:lbytes 2{b == bytes_of_int #2 (U16.v n)}

val bytes_of_int8:
    n:U8.t
  -> b:lbytes 1{b == bytes_of_int #1 (U8.v n)}

type minbytes (n:nat) = b:bytes{U32.v (length b) >= n}

val xor:
    n:u32
  -> b1:minbytes (U32.v n)
  -> b2:minbytes (U32.v n)
  -> b:bytes{length b = n}

val xor_commutative:
    n:u32
  -> b1:minbytes (U32.v n)
  -> b2:minbytes (U32.v n)
  -> Lemma (ensures (xor n b1 b2 == xor n b2 b1))
          [SMTPat (xor n b1 b2)]

val xor_append:
    b1:bytes
  -> b2:bytes{FStar.UInt.size (U32.v (length b1) + U32.v (length b2)) U32.n}
  -> x1:bytes{length x1 = length b1}
  -> x2:bytes{length x2 = length b2}
  -> Lemma (ensures (xor U32.(length b1 +^ length b2)
                        (b1 @| b2)
                        (x1 @| x2)
                    ==
                    xor (length b1) b1 x1 @| xor (length b2) b2 x2))

val xor_idempotent:
    n:u32
  -> b1:lbytes (U32.v n)
  -> b2:lbytes (U32.v n)
  -> Lemma (ensures (xor n (xor n b1 b2) b2 == b1))

val utf8_encode:
    s:string{Str.length s < pow2 30}
  -> b:bytes{U32.v (length b) <= op_Multiply 4 (Str.length s)}
