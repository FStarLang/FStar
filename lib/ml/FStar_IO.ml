exception EOF
type fd_read = in_channel
type fd_write = out_channel
let pr  = Printf.printf
let spr = Printf.sprintf
let fpr = Printf.fprintf

let print_newline = print_newline
let print_string s = pr "%s" s; flush stdout
let print_any s = output_value stdout s; flush stdout
let input_line = read_line
let input_int = read_int
let input_float = read_float
let open_read_file = open_in
let open_write_file = open_out
let close_read_file = close_in
let close_write_file = close_out
let read_line fd = try Pervasives.input_line fd with End_of_file -> raise EOF
let write_string = output_string

