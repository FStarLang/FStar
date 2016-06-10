open Char
open SBuffer

type sbytes = SInt_UInt8.uint8 buffer
type uint32 = SInt_UInt32.uint32

let create init len = create 8 init len
let index b n = index 8 b n
let upd b n v = upd 8 b n v
let sub b i len = sub 8 b i len
let blit a a_idx b b_idx len = blit 8 a a_idx b b_idx len
let split a i  = split 8 a i
let copy a len = copy 8 a len
let offset a i = offset 8 a i

let uint32_of_sbytes (b:sbytes) : uint32 =
   let v = SInt_UInt8.to_int (index b 0) + (SInt_UInt8.to_int  (index b 1) lsl 8) +
             (SInt_UInt8.to_int  (index b 2) lsl 16) + (SInt_UInt8.to_int  (index b 3) lsl 24) in
   SInt_UInt32.of_int v

let uint32s_of_sbytes (res:uint32 buffer) (b:sbytes) l =
  for i = 0 to l/4-1 do
    upd res i (SInt_UInt32.of_int (SInt_UInt8.to_int (index b (4*i)) + (SInt_UInt8.to_int (index b (4*i+1)) lsl 8) + (SInt_UInt8.to_int (index b (4*i+2)) lsl 16) + (SInt_UInt8.to_int (index b (4*i+3)) lsl 24)))
  done

let be_uint32s_of_sbytes (res:uint32 buffer) (b:sbytes) l =
  for i = 0 to l/4-1 do
    upd res i (SInt_UInt8.to_int (index b (4*i+3)) + (SInt_UInt8.to_int (index b (4*i+2)) lsl 8) + (SInt_UInt8.to_int (index b (4*i+1)) lsl 16) + (SInt_UInt8.to_int (index b (4*i)) lsl 24))
  done

let sbytes_of_uint32s (res:sbytes) (b:uint32 buffer) l =
  for i = 0 to l-1 do
    let v = SBuffer.index 0 b i in
    upd res (4*i) (SInt_UInt8.of_int (SInt_UInt32.to_int v land 255));
    upd res (4*i+1) (SInt_UInt8.of_int (((SInt_UInt32.to_int v) lsr 8) land 255));
    upd res (4*i+2) (SInt_UInt8.of_int (((SInt_UInt32.to_int v) lsr 16) land 255));
    upd res (4*i+3) (SInt_UInt8.of_int (((SInt_UInt32.to_int v) lsr 24) land 255))
  done

let be_sbytes_of_uint32s (res:sbytes) (b:uint32 buffer) l =
  for i = 0 to l-1 do
    let v = SBuffer.index 0 b i in
    upd res (4*i+3) (SInt_UInt8.of_int (SInt_UInt32.to_int v land 255));
    upd res (4*i+2) (SInt_UInt8.of_int (((SInt_UInt32.to_int v) lsr 8) land 255));
    upd res (4*i+1) (SInt_UInt8.of_int (((SInt_UInt32.to_int v) lsr 16) land 255));
    upd res (4*i)   (SInt_UInt8.of_int (((SInt_UInt32.to_int v) lsr 24) land 255))
  done

let sbytes_of_uint64 res v =
  let i = 0 in
  let mask = SInt_UInt64.of_int 0xff in
  upd res (i) (SInt_Cast.uint64_to_uint8 (SInt_UInt64.logand v mask));
  upd res (i+1) (SInt_Cast.uint64_to_uint8 (SInt_UInt64.logand (SInt_UInt64.shift_right v 8) mask));
  upd res (i+2) (SInt_Cast.uint64_to_uint8 (SInt_UInt64.logand (SInt_UInt64.shift_right v 16) mask));
  upd res (i+3) (SInt_Cast.uint64_to_uint8 (SInt_UInt64.logand (SInt_UInt64.shift_right v 24) mask));
  upd res (i+4) (SInt_Cast.uint64_to_uint8 (SInt_UInt64.logand (SInt_UInt64.shift_right v 32) mask));
  upd res (i+5) (SInt_Cast.uint64_to_uint8 (SInt_UInt64.logand (SInt_UInt64.shift_right v 40) mask));
  upd res (i+6) (SInt_Cast.uint64_to_uint8 (SInt_UInt64.logand (SInt_UInt64.shift_right v 48) mask));
  upd res (i+7) (SInt_Cast.uint64_to_uint8 (SInt_UInt64.logand (SInt_UInt64.shift_right v 56) mask))

let be_sbytes_of_uint64 res v =
  let i = 0 in
  let mask = SInt_UInt64.of_int 0xff in
  upd res (i+7) (SInt_Cast.uint64_to_uint8 (SInt_UInt64.logand v mask));
  upd res (i+6) (SInt_Cast.uint64_to_uint8 (SInt_UInt64.logand (SInt_UInt64.shift_right v 8) mask));
  upd res (i+5) (SInt_Cast.uint64_to_uint8 (SInt_UInt64.logand (SInt_UInt64.shift_right v 16) mask));
  upd res (i+4) (SInt_Cast.uint64_to_uint8 (SInt_UInt64.logand (SInt_UInt64.shift_right v 24) mask));
  upd res (i+3) (SInt_Cast.uint64_to_uint8 (SInt_UInt64.logand (SInt_UInt64.shift_right v 32) mask));
  upd res (i+2) (SInt_Cast.uint64_to_uint8 (SInt_UInt64.logand (SInt_UInt64.shift_right v 40) mask));
  upd res (i+1) (SInt_Cast.uint64_to_uint8 (SInt_UInt64.logand (SInt_UInt64.shift_right v 48) mask));
  upd res (i) (SInt_Cast.uint64_to_uint8 (SInt_UInt64.logand (SInt_UInt64.shift_right v 56) mask))

let xor_bytes (c:sbytes) (a:sbytes) (b:sbytes) l =
  for i = 0 to l-1 do
    upd c i (SInt_UInt8.logxor (index a i) (index b i))
  done

let print b =
  let s = ref "" in
  for i = 0 to b.length - 1 do
    let s' = Printf.sprintf "%X" ( (index b i))  in
    let s' = if String.length s' = 1 then "0" ^ s' else s' in
    s := !s ^ s';
  done;
  !s

let print_bytes b =
  print_string (print b); print_string "\n"
