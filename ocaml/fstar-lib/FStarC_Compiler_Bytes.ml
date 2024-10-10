let b0 n =  (n land 0xFF)
let b1 n =  ((n lsr 8) land 0xFF)
let b2 n =  ((n lsr 16) land 0xFF)
let b3 n =  ((n lsr 24) land 0xFF)

let dWw1 n = BatInt64.to_int (BatInt64.logand (BatInt64.shift_right n 32) 0xFFFFFFFFL)
let dWw0 n = BatInt64.to_int (BatInt64.logand n 0xFFFFFFFFL)

type bytes = int array

let f_encode f (b:bytes) = String.concat "" (Array.to_list (Array.map f b))
let length (b:bytes) = BatArray.length b
let get (b:bytes) n = Z.of_int (BatArray.get b (Z.to_int n))
let make (f : _ -> Z.t) n = BatArray.init (Z.to_int n) (fun i -> Z.to_int (f (Z.of_int i)))
let zero_create n : bytes = BatArray.create n 0

let sub ( b:bytes) s l = BatArray.sub b s l
let set = BatArray.set
let blit (a:bytes) b c d e = BatArray.blit a b c d e
let string_as_unicode_bytes (s:string) = FStarC_Compiler_Util.unicode_of_string s
let utf8_bytes_as_string (b:bytes) = FStarC_Compiler_Util.string_of_unicode b
let unicode_bytes_as_string (b:bytes) = FStarC_Compiler_Util.string_of_unicode b
let compare (b1:bytes) (b2:bytes) = compare b1 b2

let to_intarray (b:bytes) = b
let of_intarray (arr:int array) = arr

let string_as_utf8_bytes (s:string) = FStarC_Compiler_Util.unicode_of_string s

let append (b1: bytes) (b2:bytes) = BatArray.append b1 b2

type bytebuf =
    { mutable bbArray: bytes;
      mutable bbCurrent: int }

module Bytebuf = struct
  let create sz =
    { bbArray=zero_create sz;
      bbCurrent = 0; }

  let ensure_bytebuf buf new_size =
    let old_buf_size = BatArray.length buf.bbArray in
    if new_size > old_buf_size then (
      let old = buf.bbArray in
      buf.bbArray <- zero_create (max new_size (old_buf_size * 2));
      blit old 0 buf.bbArray 0 buf.bbCurrent
    )

  let close buf = sub buf.bbArray 0 buf.bbCurrent

  let emit_int_as_byte buf i =
    let new_size = buf.bbCurrent + 1 in
    ensure_bytebuf buf new_size;
    set buf.bbArray buf.bbCurrent i;
    buf.bbCurrent <- new_size

  let emit_byte buf (b:char) = emit_int_as_byte buf (int_of_char b)
  let emit_bool_as_byte buf (b:bool) = emit_int_as_byte buf (if b then 1 else 0)

  let emit_bytes buf i =
    let n = length i in
    let new_size = buf.bbCurrent + n in
    ensure_bytebuf buf new_size;
    blit i 0 buf.bbArray buf.bbCurrent n;
    buf.bbCurrent <- new_size

  let emit_i32_as_u16 buf n =
    let new_size = buf.bbCurrent + 2 in
    ensure_bytebuf buf new_size;
    set buf.bbArray buf.bbCurrent (b0 n);
    set buf.bbArray (buf.bbCurrent + 1) (b1 n);
    buf.bbCurrent <- new_size

  (* let emit_u16 buf (x:uint16) = emit_i32_as_u16 buf (BatInt64.to_int x) *)

  let fixup_i32 bb pos n =
    set bb.bbArray pos (b0 n);
    set bb.bbArray (pos + 1) (b1 n);
    set bb.bbArray (pos + 2) (b2 n);
    set bb.bbArray (pos + 3) (b3 n)

  let emit_i32 buf n =
    let new_size = buf.bbCurrent + 4 in
    ensure_bytebuf buf new_size;
    fixup_i32 buf buf.bbCurrent n;
    buf.bbCurrent <- new_size

  let emit_i64 buf x =
    emit_i32 buf (dWw0 x);
    emit_i32 buf (dWw1 x)

  let emit_intarray_as_bytes buf arr =
    let n = BatArray.length arr in
    let new_size = buf.bbCurrent + n in
    ensure_bytebuf buf new_size;
    let bbarr = buf.bbArray in
    let bbbase = buf.bbCurrent in
    for i= 0 to n - 1 do set bbarr (bbbase + i) (BatArray.get arr i) done;
    buf.bbCurrent <- new_size

  let length bb = bb.bbCurrent
  let position bb = bb.bbCurrent

end

let create i = Bytebuf.create i
let close t = Bytebuf.close t
let emit_int_as_byte t i = Bytebuf.emit_int_as_byte t (Z.to_int i)
let emit_bytes t b = Bytebuf.emit_bytes t b

let length x = Z.of_int (length x)
