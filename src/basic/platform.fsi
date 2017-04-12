module FStar.Platform
open FStar.All
type sys =
| Windows
| Posix

val system : sys
val exe : string -> string

(* true if the fstar compiler is compiled from sources extracted to ocaml, false otherwise *)
val is_fstar_compiler_using_ocaml : bool

(* initialize the OCaml GC alarm in case user specifies --print_ocaml_gc_statistics *)
val init_print_ocaml_gc_statistics : unit -> unit
