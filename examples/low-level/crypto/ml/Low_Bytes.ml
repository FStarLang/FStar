open FStar_Buffer

type size = int
type 'a bytes_ = int buffer

type bytes = int buffer
type u16s = int buffer
type u32s = int buffer
type u64s = int buffer

type u16 = FStar_UInt16.t
type u32 = FStar_UInt32.t
type u64 = FStar_UInt64.t
                
let bytes_to_u16s b = b
let bytes_to_u32s b = b
let bytes_to_u64s b = b
let u16s_to_bytes b = b
let u32s_to_bytes b = b
let u64s_to_bytes b = b

(* SizeOf assumptions *)
let size_of x = -1

let create_8 len =
  FStar_Buffer.create 0 len
let create_16 len =
  FStar_Buffer.create 0 (2*len)
let create_32 len =
  FStar_Buffer.create 0 (4*len)
let create_64 len =
  FStar_Buffer.create 0 (8*len)

let read_8 b i =
  index b i                         
let read_16 b i =
  let n = 2 in
  let b0 = index b (n*i) in
  let b1 = index b (n*i+1) in
  b0 + (b1 lsl 8)
let read_32 b i =
  let n = 4 in
  let b0 = index b (n*i) in
  let b1 = index b (n*i+1) in
  let b2 = index b (n*i+2) in
  let b3 = index b (n*i+3) in
  b0 + (b1 lsl 8) + (b2 lsl 16) + (b3 lsl 24)
let read_64 b i =
  let n = 8 in
  let b0 = FStar_UInt64.shift_left (FStar_Int_Cast.uint8_to_uint64 (index b (n*i))) 0 in
  let b1 = FStar_UInt64.shift_left (FStar_Int_Cast.uint8_to_uint64 (index b (n*i+1))) 8 in
  let b2 = FStar_UInt64.shift_left (FStar_Int_Cast.uint8_to_uint64 (index b (n*i+2))) 16 in
  let b3 = FStar_UInt64.shift_left (FStar_Int_Cast.uint8_to_uint64 (index b (n*i+3))) 24 in
  let b4 = FStar_UInt64.shift_left (FStar_Int_Cast.uint8_to_uint64 (index b (n*i+4))) 32 in
  let b5 = FStar_UInt64.shift_left (FStar_Int_Cast.uint8_to_uint64 (index b (n*i+5))) 40 in
  let b6 = FStar_UInt64.shift_left (FStar_Int_Cast.uint8_to_uint64 (index b (n*i+6))) 48 in
  let b7 = FStar_UInt64.shift_left (FStar_Int_Cast.uint8_to_uint64 (index b (n*i+7))) 56 in
  FStar_UInt64.add b0
                   (FStar_UInt64.add b1
                                     (FStar_UInt64.add b2
                                                       (FStar_UInt64.add b3
                                                                         (FStar_UInt64.add b4
                                                                                           (FStar_UInt64.add b5
                                                                                                             (FStar_UInt64.add b6 b7) ) ) ) ) )

let write_8 b i z =
  upd b i z
let write_16 b i z =
  let n = 2 in
  let b0 = z land 255 in
  let b1 = (z lsr 8) land 255 in
  upd b (n*i+0) b0;
  upd b (n*i+1) b1
let write_32 b i z =
  let n = 4 in
  let b0 = z land 255 in
  let b1 = (z lsr 8) land 255 in
  let b2 = (z lsr 16) land 255 in
  let b3 = (z lsr 24) land 255 in
  upd b (n*i+0) b0;
  upd b (n*i+1) b1;
  upd b (n*i+2) b2;
  upd b (n*i+3) b3
let write_64 b i z =
  let n = 8 in
  let b0 = FStar_Int_Cast.uint64_to_uint8 z in
  let b1 = FStar_Int_Cast.uint64_to_uint8 (FStar_UInt64.shift_right z 8) in
  let b2 = FStar_Int_Cast.uint64_to_uint8 (FStar_UInt64.shift_right z 16) in
  let b3 = FStar_Int_Cast.uint64_to_uint8 (FStar_UInt64.shift_right z 24) in
  let b4 = FStar_Int_Cast.uint64_to_uint8 (FStar_UInt64.shift_right z 32) in
  let b5 = FStar_Int_Cast.uint64_to_uint8 (FStar_UInt64.shift_right z 40) in
  let b6 = FStar_Int_Cast.uint64_to_uint8 (FStar_UInt64.shift_right z 48) in
  let b7 = FStar_Int_Cast.uint64_to_uint8 (FStar_UInt64.shift_right z 56) in
  upd b (n*i+0) b0;
  upd b (n*i+1) b1;
  upd b (n*i+2) b2;
  upd b (n*i+3) b3;
  upd b (n*i+4) b4;
  upd b (n*i+5) b5;
  upd b (n*i+6) b6;
  upd b (n*i+7) b7

let memcpy_8 src srci dest desti len =
  for i = 0 to len-1 do
    upd dest (desti + i) (index src (srci+i))
  done
let memcpy_16 src srci dest desti len =
  memcpy_8 src (2*srci) dest (2*desti) (2*len)
let memcpy_32 src srci dest desti len =
  memcpy_8 src (4*srci) dest (4*desti) (4*len)
let memcpy_64 src srci dest desti len =
  memcpy_8 src (8*srci) dest (8*desti) (8*len)

let sub_8 b i len : bytes =
  sub b i len
let sub_16 b i len : u16s =
  sub b (2*i) (2*len)
let sub_32 b i len : u32s =
  sub b (4*i) (4*len)
let sub_64 b i len : u64s =
  sub b (8*i) (8*len)
let offset_8 b i = 
  offset b i
let offset_16 b i len =
  offset b (2*i)
let offset_32 b i len =
  offset b (4*i)
let offset_64 b i len =
  offset b (8*i)
