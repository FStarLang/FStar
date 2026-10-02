module BytesFS

/// Section 122.17.  [FStar.Bytes] on the F# backend.  The realization there is
/// a [byte[]] and not the OCaml realization's [string], so this exercises the
/// places where the two could disagree: structural equality on the
/// realization, the big-endian integer encodings, the two hex readings and
/// the UTF-8 round trip.  Every check states its own answer, so the F# leg --
/// which runs the program but does not diff its output -- fails on a wrong
/// one instead of printing it.

open FStar.All
module B = FStar.Bytes

let check (name : string) (actual : string) (expect : string) : ML unit =
  if actual = expect
  then FStar.IO.print_string (name ^ ": " ^ actual ^ "\n")
  else failwith (name ^ ": expected " ^ expect ^ ", got " ^ actual)

let yes (name : string) (b : bool) : ML unit =
  check name (string_of_bool b) "true"

let dec (b : B.bytes) : ML string =
  match B.iutf8_opt b with
  | Some s -> s
  | None -> "rejected"

let main () : ML unit =
  let b = B.create 3ul 7uy in
  check "hex_of_bytes" (B.hex_of_bytes b) "070707";
  check "print_bytes" (B.print_bytes b) "070707";
  yes "bytes_of_hex" (B.bytes_of_hex (B.hex_of_bytes b) = b);
  yes "append" (B.len (B.append b b) = 6ul);
  check "abyte/twobytes"
    (B.hex_of_bytes (B.append (B.abyte 1uy) (B.twobytes (2uy, 3uy)))) "010203";
  check "bytes_of_int32" (B.hex_of_bytes (B.bytes_of_int32 305419896ul))
    "12345678";
  check "bytes_of_int16" (B.hex_of_bytes (B.bytes_of_int16 4660us)) "1234";
  check "bytes_of_int8" (B.hex_of_bytes (B.bytes_of_int8 171uy)) "ab";
  yes "int32_of_bytes"
    (B.int32_of_bytes (B.bytes_of_int32 305419896ul) = 305419896ul);
  yes "repr_bytes" (B.repr_bytes 255 = 1 && B.repr_bytes 256 = 2);
  check "xor" (B.hex_of_bytes (B.xor 3ul b (B.create 3ul 255uy))) "f8f8f8";
  check "hex_of_string" (B.hex_of_string "AB") "4142";
  check "string_of_hex" (B.string_of_hex "4142") "AB";
  check "utf8_encode" (B.hex_of_bytes (B.utf8_encode "h\u00e9")) "68c3a9";
  check "iutf8_opt" (dec (B.utf8_encode "h\u00e9")) "h\u00e9";
  check "iutf8_opt/bad" (dec (B.abyte 255uy)) "rejected"
