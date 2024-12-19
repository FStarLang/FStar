module FStarC.Platform
open FStarC.Compiler.Effect

type sys =
| Windows
| Posix

val system : sys
val exe : string -> string
