module FStar.IO
open List

exception EOF
assume type fd_read
assume type fd_write

assume val print_string : string -> unit
assume val print_any : 'a -> unit
assume val format : string -> list string -> string
assume val hex_string_of_byte : char -> string
assume val string_of_char : char -> string
assume val string_of_float : float -> string
assume val string_of_int : int -> string
assume val string_of_int64 : int64 -> string
assume val int_of_string : string -> int
assume val input_line : unit -> string
assume val input_int : unit -> int
assume val input_float : unit -> float
assume val open_read_file : string -> fd_read
assume val open_write_file : string -> fd_write
assume val close_read_file : fd_read -> unit
assume val close_write_file : fd_write -> unit
assume val read_line : fd_read -> string
assume val write_string : fd_write -> string -> unit

