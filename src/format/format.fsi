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
type value = Char of char | String of string | Int of int | Float of float

val (<<) : formatter -> value -> unit
