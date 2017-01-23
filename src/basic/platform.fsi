module FStar.Platform

type sys =
| Windows
| Posix

val system : sys
val exe : string -> string
