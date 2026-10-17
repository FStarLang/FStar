(* Model implementation of FStar.IO: verified, but never extracted (the real implementation is native).
   Output is discarded and input is always empty. *)
module FStar.IO

open FStar.All

type fd_read = | FdRead : fd_read
type fd_write = | FdWrite : fd_write

let stdin = FdRead
let stdout = FdWrite
let stderr = FdWrite

let print_newline _ = ()
let print_string _ = ()
let print_uint8 _ = ()
let print_uint16 _ = ()
let print_uint32 _ = ()
let print_uint64 _ = ()
let print_uint8_dec _ = ()
let print_uint16_dec _ = ()
let print_uint32_dec _ = ()
let print_uint64_dec _ = ()
let print_uint8_hex_pad _ = ()
let print_uint16_hex_pad _ = ()
let print_uint32_hex_pad _ = ()
let print_uint64_hex_pad _ = ()
let print_uint8_dec_pad _ = ()
let print_uint16_dec_pad _ = ()
let print_uint32_dec_pad _ = ()
let print_uint64_dec_pad _ = ()
let print_any _ = ()
let input_line _ = ""
let input_int _ = 0
let input_float _ = FStar.Float64.zero
let open_read_file _ = FdRead
let open_write_file _ = FdWrite
let close_read_file _ = ()
let close_write_file _ = ()
let read_line _ = ""
let write_string _ _ = ()
let debug_print_string _ = false
