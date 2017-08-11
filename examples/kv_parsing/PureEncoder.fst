module PureEncoder

open FStar.Seq
module U16 = FStar.UInt16
module U32 = FStar.UInt32
module Cast = FStar.Int.Cast
module List = FStar.List.Tot

open KeyValue
open PureParser

(*! Serializing a key-value store *)

(* TODO: somewhat minor, but standardize on a name for these (writer, encoder,
serializer, emitter) *)

val u16_to_be: U16.t -> b:bytes{length b == 2}
let u16_to_be (n:U16.t) = create 1 (Cast.uint16_to_uint8 (U16.shift_right n 8ul)) `append`
                          create 1 (Cast.uint16_to_uint8 (U16.rem n 256us))

assume val u32_to_be: U32.t -> b:bytes{length b == 4}

let encode_u16_array (len:U16.t) (b:bytes{length b == U16.v len}) : bytes =
  u16_to_be len `append` b

let encode_u32_array (len:U32.t) (b:bytes{length b == U32.v len}) : bytes =
  u32_to_be len `append` b

val encode_entry: encoded_entry -> bytes
let encode_entry e = encode_u16_array e.key_len e.key `append`
                     encode_u32_array e.val_len e.value

val encode_many : #t:Type -> l:list t -> enc:(t -> bytes) -> n:nat{n <= List.length l} -> bytes
let rec encode_many #t l enc n =
  match n with
  | 0 -> Seq.createEmpty
  | _ -> enc (List.hd l) `append`
        encode_many (List.tail l) enc (n-1)

val encode_store : s:store -> bytes
let encode_store s =
  u32_to_be (s.num_entries) `append`
  encode_many s.entries encode_entry (U32.v s.num_entries)
