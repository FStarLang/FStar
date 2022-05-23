exception EOF
type fd_read = in_channel
type fd_write = out_channel
let stdin = stdin
let stdout = stdout
let stderr = stderr

let pr  = Printf.printf
let spr = Printf.sprintf
let fpr = Printf.fprintf

let print_newline = print_newline
let print_string s = pr "%s" s; flush stdout


(* let print_nat s =
 *   pr "%x" s;
 *   flush stdout
 *
 * let print_nat_dec s =
 *   pr "%u" s;
 *   flush stdout *)

let print_via (f:'a -> string) (x:'a) : unit =
    print_string (f x);
    flush stdout

let print_uint8          = print_via FStar_UInt8.to_string_hex
let print_uint16         = print_via FStar_UInt16.to_string_hex
let print_uint32         = print_via FStar_UInt32.to_string_hex
let print_uint64         = print_via FStar_UInt64.to_string_hex

let print_uint8_dec      = print_via FStar_UInt8.to_string
let print_uint16_dec     = print_via FStar_UInt16.to_string
let print_uint32_dec     = print_via FStar_UInt32.to_string
let print_uint64_dec     = print_via FStar_UInt64.to_string

let print_uint8_hex_pad  = print_via FStar_UInt8.to_string_hex_pad
let print_uint16_hex_pad = print_via FStar_UInt16.to_string_hex_pad
let print_uint32_hex_pad = print_via FStar_UInt32.to_string_hex_pad
let print_uint64_hex_pad = print_via FStar_UInt64.to_string_hex_pad


let __zeropad n s =
    String.make (n - String.length s) '0' ^ s

(* The magic numbers in these dec_pad functions are the precomputed
 * string lengths of the maximum number when printed in decimal.
 *
 * - length "255" = 3
 * - length "65535" = 5
 * - length "4294967296" = 10
 * - length "18446744073709551616" = 20
 *)
let print_uint8_dec_pad n =
    let s = FStar_UInt8.to_string n in
    print_string (__zeropad 3 s)

let print_uint16_dec_pad n =
    let s = FStar_UInt16.to_string n in
    print_string (__zeropad 5 s)

let print_uint32_dec_pad n =
    let s = FStar_UInt32.to_string n in
    print_string (__zeropad 10 s)

let print_uint64_dec_pad n =
    let s = FStar_UInt64.to_string n in
    print_string (__zeropad 20 s)

let print_any s = output_value stdout s; flush stdout
let input_line = read_line
let input_int () = Z.of_int (read_int ())
let input_float = read_float
let open_read_file = open_in
let open_write_file = open_out
let close_read_file = close_in
let close_write_file = close_out
let read_line fd = try Stdlib.input_line fd with End_of_file -> raise EOF
let write_string = output_string

let debug_print_string s = print_string s; false
