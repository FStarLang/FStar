(* -------------------------------------------------------------------- *)
module FSharp.OCaml.Format

(* -------------------------------------------------------------------- *)
type formatter

(* -------------------------------------------------------------------- *)
val open_box    : formatter -> int -> unit
val open_hbox   : formatter -> unit
val open_vbox   : formatter -> int -> unit
val open_hvbox  : formatter -> int -> unit
val open_hovbox : formatter -> int -> unit

val closebox : formatter -> unit

(* -------------------------------------------------------------------- *)
val print_space   : formatter -> unit
val print_cut     : formatter -> unit
val print_brk     : formatter -> int -> int -> unit
val print_flush   : formatter -> unit
val print_newline : formatter -> unit

(* -------------------------------------------------------------------- *)
val print_char   : formatter -> char   -> unit
val print_string : formatter -> string -> unit
val print_int    : formatter -> int    -> unit
val print_float  : formatter -> float  -> unit
