module FStar.Platform
open FStar.All
type sys =
| Windows
| Posix

val system : sys
val exe : string -> string
