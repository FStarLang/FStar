exception EOF
type fd_read = in_channel
type fd_write = out_channel
let pr  = Printf.printf
let spr = Printf.sprintf
let fpr = Printf.fprintf

let print_newline = print_newline
let print_string s = pr "%s" s; flush stdout
let print_uint8 s = pr "%x" (FStar_UInt8.to_int s); flush stdout
let print_uint8_dec s = pr "%s" (FStar_UInt8.to_string s); flush stdout
let print_uint32 s = pr "%x" (FStar_UInt32.to_int s); flush stdout
let print_uint32_dec s = pr "%s" (FStar_UInt32.to_string s); flush stdout
let print_uint64 s = pr "%s" (let fs = FStar_UInt64.to_string_hex s in
                              String.sub fs 2 (String.length fs - 2)); flush stdout
let print_uint64_dec s = pr "%s" (FStar_UInt64.to_string s); flush stdout
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
