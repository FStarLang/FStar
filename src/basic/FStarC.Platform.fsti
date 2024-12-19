module FStarC.Platform
open FStarC.Compiler.Effect

type sys =
| Windows
| Posix

val system : sys
val exe : string -> string

(* true when we are running in Cygwin. Note: system will return 'Windows' in this case *)
val is_cygwin : bool
