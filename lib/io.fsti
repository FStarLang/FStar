module FStar.IO
exception EOF
type fd_read
type fd_write

val print_newline : unit -> unit
val print_string : string -> unit
val print_any : 'a -> unit
val input_line : unit -> string
val input_int : unit -> int
val input_float : unit -> float
val open_read_file : string -> fd_read
val open_write_file : string -> fd_write
val close_read_file : fd_read -> unit
val close_write_file : fd_write -> unit
val read_line : fd_read -> string
val write_string : fd_write -> string -> unit
