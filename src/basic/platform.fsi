module Microsoft.FStar.Platform

type system =
| Windows
| Posix

val system : system
val exe : string -> string
