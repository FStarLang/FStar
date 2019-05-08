exception EOF
type fd_read = in_channel
type fd_write = out_channel
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


let print_uint8 s =
  let s' = FStar_UInt8.to_int s in
  pr "%x" s';
  flush stdout

let print_uint8_dec s =
  pr "%s" (FStar_UInt8.to_string s);
  flush stdout

let print_uint32 s =
  pr "%x" (FStar_UInt32.to_int s);
  flush stdout

let print_uint32_dec s =
  pr "%s" (FStar_UInt32.to_string s);
  flush stdout

let print_uint64 s =
  let fs = FStar_UInt64.to_string_hex s in
  let s' = String.sub fs 2 (String.length fs - 2) in
  pr "%s" s';
  flush stdout

let print_uint64_dec s =
  pr "%s" (FStar_UInt64.to_string s);
  flush stdout


let print_uint8_hex_pad s =
  let n = FStar_Int_Cast.uint8_to_uint64 s in
  let fs = FStar_UInt64.to_string_hex n in
  let s' = String.sub fs 2 (String.length fs - 2) in
  let l = 2 - String.length s' in
  let r = (String.make l '0') ^ s' in
  pr "%s" r;
  flush stdout

let print_uint8_dec_pad s =
  let s' = FStar_UInt8.to_string s in
  let l = 2 - String.length s' in
  let r = (String.make l '0') ^ s' in
  pr "%s" r;
  flush stdout

let print_uint32_hex_pad s =
  let n = FStar_Int_Cast.uint32_to_uint64 s in
  let fs = FStar_UInt64.to_string_hex n in
  let s' = String.sub fs 2 (String.length fs - 2) in
  let l = 8 - String.length s' in
  let r = (String.make l '0') ^ s' in
  pr "%s" r;
  flush stdout

let print_uint32_dec_pad s =
  let s' = FStar_UInt32.to_string s in
  let l = 8 - String.length s' in
  let r = (String.make l '0') ^ s' in
  pr "%s" r;
  flush stdout

let print_uint64_hex_pad s =
  let fs = FStar_UInt64.to_string_hex s in
  let s' = String.sub fs 2 (String.length fs - 2) in
  let l = 16 - String.length s' in
  let r = (String.make l '0') ^ s' in
  pr "%s" r;
  flush stdout

let print_uint64_dec_pad s =
  let s' = FStar_UInt64.to_string s in
  let l = 16 - String.length s' in
  let r = (String.make l '0') ^ s' in
  pr "%s" r;
  flush stdout


let print_any s = output_value stdout s; flush stdout
let input_line = read_line
let input_int () = Z.of_int (read_int ())
let input_float = read_float
let open_read_file = open_in
let open_write_file = open_out
let close_read_file = close_in
let close_write_file = close_out
let read_line fd = try Pervasives.input_line fd with End_of_file -> raise EOF
let write_string = output_string

let debug_print_string s = print_string s; false
