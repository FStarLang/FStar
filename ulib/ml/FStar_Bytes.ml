module U8 = FStar_UInt8
module U16 = FStar_UInt16
module U32 = FStar_UInt32
module U64 = FStar_UInt64

type u8 = U8.t
type u16 = U16.t
type u32 = U32.t

type byte = u8

type bytes = string
type cbytes = string (* not in FStar.Bytes *)

let len (b:bytes) = U32.of_native_int (String.length b)
let length (b:bytes) = Z.of_int (String.length b)

let reveal (b:bytes) = ()
let length_reveal (x:bytes) = ()
let hide s = ()
let hide_reveal (x:bytes) = ()
let reveal_hide s = ()

type 'a lbytes = bytes
type 'a lbytes32 = bytes
type kbytes = bytes

let empty_bytes = ""
let empty_unique (b:bytes) = ()

let get (b:bytes) (pos:u32) = int_of_char (String.get b (Z.to_int (U32.to_int pos)))
let op_String_Access = get

let index (b:bytes) (i:Z.t) = get b (U32.uint_to_t i)

type ('b1, 'b2) equal = unit

let extensionality (b1:bytes) (b2:bytes) = ()

let create (len:u32) (v:byte)  = String.make (U32.to_native_int len) (char_of_int v)
let create_ (len:Z.t) (v:byte) = String.make (Z.to_int  len) (char_of_int v)

let init (len:u32) (f:u32 -> byte) =
  String.init (U32.to_native_int len)
    (fun (i:int) ->
        let b : byte = f (U32.of_native_int i) in
        char_of_int b)

let abyte (b:byte) = create (U32.of_native_int 1) b
let twobytes (bs:(byte * byte)) =
  init (U32.of_native_int 2) (fun i -> if i = U32.of_native_int 0 then fst bs else snd bs)

let append (b1:bytes) (b2:bytes) = b1 ^ b2
let op_At_Bar = append

let slice (b:bytes) (s:u32) (e:u32) =
    String.sub b (U32.to_native_int s) (U32.to_native_int (U32.sub e s))
let slice_ (b:bytes) (s:Z.t) (e:Z.t) =
    slice b (U32.uint_to_t s) (U32.uint_to_t e)

let sub (b:bytes) (s:u32) (l:u32) =
    String.sub b (U32.to_native_int s) (U32.to_native_int l)

let split (b:bytes) (k:u32) =
    sub b (U32.of_native_int 0) k,
    sub b k (U32.sub (U32.of_native_int (String.length b)) k)
let split_ (b:bytes) (k:Z.t) =
    split b (U32.of_int k)

let fits_in_k_bytes (n:Z.t) (k:Z.t) = (* expects k to fit in an int *)
    Z.leq Z.zero n &&
    Z.leq n (Z.of_int (BatInt.pow 2 (8 * Z.to_int k)))
type 'a uint_k = Z.t

let rec repr_bytes (n:Z.t) =
  if Z.to_int n < 256 then Z.of_int 1
  else Z.add (Z.of_int 1) (repr_bytes (Z.div n (Z.of_int 256)))

let lemma_repr_bytes_values (n:Z.t) = ()
let repr_bytes_size (k:Z.t) (n:'a uint_k) = ()
let int_of_bytes (b:bytes) =
    let x = ref Z.zero in
    let len = String.length b in
    let n = Z.of_int 256 in
    for y = 0 to len-1 do
        x := Z.add (Z.mul n !x) (Z.of_int (get b (U32.of_native_int y)))
    done;
    !x

let bytes_of_int (nb:Z.t) (i:Z.t) =
  let nb = Z.to_int nb in
  let i = Z.to_int64 i in
  if Int64.compare i Int64.zero < 0 then failwith "Negative 64bit.";
  let rec put_bytes bb lb n =
    if lb = 0 then failwith "not enough bytes"
    else
      begin
        let lown = Int64.logand n (Int64.of_int 255) in
        Bytes.set bb (lb-1) (char_of_int (Int64.to_int lown));
        let ns = Int64.div n (Int64.of_int 256) in
        if Int64.compare ns Int64.zero > 0 then
           put_bytes bb (lb-1) ns
        else bb
      end
  in
  let b = Bytes.make nb (char_of_int 0) in
  Bytes.to_string (put_bytes b nb i)

let int_of_bytes_of_int (k:Z.t) (n:'a uint_k) = ()
let bytes_of_int_of_bytes (b:bytes) = ()

let int32_of_bytes (b:bytes) =
    Z.to_int (int_of_bytes b)

let int16_of_bytes (b:bytes) =
    Z.to_int (int_of_bytes b)

let int8_of_bytes (b:bytes) =
    Z.to_int (int_of_bytes b)

let bytes_of_int32 (n:U32.t) =
    bytes_of_int (Z.of_int 4) (U32.to_int n)

let bytes_of_int16 (n:U32.t) =
    bytes_of_int (Z.of_int 2) (U32.to_int n)

let bytes_of_int8 (n:U32.t) =
    bytes_of_int (Z.of_int 1) (U32.to_int n)

type 'a minbytes = bytes

let xor (len:U32.t) (s1:'a minbytes) (s2:'b minbytes) : bytes =
    let f (i:u32) : byte =
        let l = int_of_char s1.[U32.to_native_int i] in
        let r = int_of_char s2.[U32.to_native_int i] in
        l lxor r
    in
    init len f

let xor_ (len:Z.t) = xor (U32.of_int len)

let xor_commutative (n:U32.t) (b1: 'a minbytes) (b2: 'b minbytes) = ()
let xor_append (b1:bytes) (b2:bytes) (x1:bytes) (b2:bytes) = ()
let xor_idempotent (n:U32.t) (b1:bytes) (b2:bytes) = ()

(*********************************************************************************)
(* Under discussion *)
let utf8 (x:string) : bytes = x (* TODO: use Camomile *)
let utf8_encode = utf8
let iutf8 (x:bytes) : string = x (* TODO: use Camomile *)
let iutf8_opt (x:bytes) : string option = Some (x)
(*********************************************************************************)

(* Some helpers to deal with the conversation from hex literals to bytes and
 * conversely. Mostly for tests. *)

let digit_to_int c = match c with
  | '0'..'9' -> Char.code c - Char.code '0'
  | 'a'..'f' -> 10 + Char.code c - Char.code 'a'
  | _ -> failwith "hex_to_char: invalid hex digit"

let hex_to_char a b =
  Char.chr ((digit_to_int a) lsl 4 + digit_to_int b)

let char_to_hex c =
  let n = Char.code c in
  let digits = "0123456789abcdef" in
  digits.[n lsr 4], digits.[n land 0x0f]

let string_of_hex s =
  let n = String.length s in
  if n mod 2 <> 0 then
     failwith "string_of_hex: invalid length"
  else
    let res = Bytes.create (n/2) in
    let rec aux i =
      if i >= n then ()
      else (
        Bytes.set res (i/2) (hex_to_char s.[i] s.[i+1]);
        aux (i+2)
      )
    in
    aux 0;
    res
let bytes_of_hex s = Bytes.to_string (string_of_hex s)

let hex_of_string s =
  let n = String.length s in
  let buf = Buffer.create n in
  for i = 0 to n - 1 do
    let d1,d2 = char_to_hex s.[i] in
    Buffer.add_char buf d1;
    Buffer.add_char buf d2;
  done;
  Buffer.contents buf
let hex_of_bytes b = hex_of_string b

let print_bytes (s:bytes) : string =
  let b = Buffer.create 1024 in
  for i = 0 to String.length s - 1 do
    Buffer.add_string b (Printf.sprintf "%02X" (int_of_char s.[i]));
  done;
  Buffer.contents b

let string_of_bytes b = b
let bytes_of_string s = s

(*********************************************************************************)
(* OLD *)
(*********************************************************************************)

let cbyte (b:bytes) =
  try int_of_char (String.get b 0)
  with _ -> failwith "cbyte: called on empty string"

let cbyte2 (b:bytes) =
  try (int_of_char (String.get b 0), int_of_char (String.get b 1))
  with _ -> failwith "cbyte2: need at least length 2"

let index (b:bytes) i =
  try int_of_char (String.get b (Z.to_int i))
  with _ -> failwith "index: called out of bound"

let get_cbytes (b:bytes) = b
let abytes (ba:cbytes) = ba
let abyte (ba:byte) = String.make 1 (char_of_int ba)
let abyte2 (ba1,ba2) =
  String.init 2 (fun i -> if i = 0 then char_of_int ba1 else char_of_int ba2)
  
let split_eq = split

let createBytes len (value:int) : bytes =
    let len = Z.to_int len in
    try abytes (String.make len (char_of_int value))
    with _ -> failwith "Default integer for createBytes was greater than max_value"

let initBytes len f : bytes =
    let len = Z.to_int len in
    try abytes (String.init len (fun i -> char_of_int (f (Z.of_int i))))
    with _ -> failwith "Platform.Bytes.initBytes: invalid char returned"

let equalBytes (b1:bytes) (b2:bytes) = b1 = b2

let split2 (b:bytes) i j : bytes * bytes * bytes =
  let b1, b2 = split b i in
  let b2a, b2b = split b2 j in
  (b1, b2a, b2b)

let byte_of_int i = Z.to_int i
